(* Lark0 所有权检查：移动后使用、借用不可移出、inout 排他性、遍历/匹配期间冻结。
   引用不可存储这条规则由此自然成立：只读借用（LRead）的值永远不能进入“拥有”位置。 *)
open Ast
module IS = Set.Make (Int)

(* Discard：值被丢弃（语句位置）。与代码生成一一对应：丢弃的分支不移动任何东西。 *)
type mode = Owning | Reading | Discard

(* if / match / 块的分支用什么模式求值；必须与 codegen 的 owned / read / discard 保持一致 *)
let arm_mode m ety =
  if ety = TUnit || ety = TNever then Discard
  else match m with
    | Owning -> Owning
    | Discard -> Discard
    | Reading -> if is_copy ety then Reading else Owning

type ctx = {
  env : Check.env;
  fn : fn_decl;
  mutable loop_depth : int;
  mutable frozen : IS.t;
  mutable breaks : IS.t option list;   (* 当前循环里各个 break 处的状态 *)
  mutable conts : IS.t option list;    (* 当前循环里各个 continue 处的状态 *)
}

let loc c vid = Hashtbl.find c.fn.locals vid

let rec root e = match e.e with
  | Var _ -> Some e.vid
  | Field (b, _) | Index (b, _) -> root b
  | _ -> None

let union a b = match a, b with
  | None, x | x, None -> x
  | Some a, Some b -> Some (IS.union a b)

(* 表达式里出现过的所有局部变量 *)
let rec vars_of acc e =
  match e.e with
  | Var _ -> IS.add e.vid acc
  | Int _ | Bool _ | Str _ | Break | Continue | Return None -> acc
  | Interp es | List es -> List.fold_left vars_of acc es
  | Field (b, _) | Unary (_, b) | Return (Some b) -> vars_of acc b
  | Index (a, b) | Binary (_, a, b) -> vars_of (vars_of acc a) b
  | Call (_, args) -> List.fold_left (fun acc a -> vars_of acc a.value) acc args
  | Method (r, _, args) -> List.fold_left (fun acc a -> vars_of acc a.value) (vars_of acc r) args
  | If (c, t, e) ->
    let acc = vars_of_block (vars_of acc c) t in
    (match e with Some b -> vars_of_block acc b | None -> acc)
  | Match (_, s, arms) -> List.fold_left (fun acc (a : arm) -> vars_of acc a.body) (vars_of acc s) arms
  | Block b -> vars_of_block acc b

and vars_of_block acc b =
  let acc = List.fold_left vars_of_stmt acc b.stmts in
  match b.tail with Some e -> vars_of acc e | None -> acc

and vars_of_stmt acc s =
  match s.s with
  | SExpr e -> vars_of acc e
  | SAssign (t, _, r, _) -> vars_of (vars_of acc t) r
  | SForCond (c, b) -> vars_of_block (match c with Some c -> vars_of acc c | None -> acc) b
  | SForRange (_, _, a, b, body) -> vars_of_block (vars_of (vars_of acc a) b) body
  | SForEach (_, _, it, body) -> vars_of_block (vars_of acc it) body

let with_frozen c r f =
  let saved = c.frozen in
  (match r with Some v -> c.frozen <- IS.add v c.frozen | None -> ());
  let res = f () in
  c.frozen <- saved;
  res

let in_loop c f =
  c.loop_depth <- c.loop_depth + 1;
  let res = f () in
  c.loop_depth <- c.loop_depth - 1;
  res

(* 循环：允许移走循环外的变量，但必须在本轮结束前（以及每个 continue 之前）重新赋值。
   break 处的状态并入循环之后的状态。 *)
let loop c pos st (body : IS.t option -> IS.t option) =
  match st with
  | None -> None
  | Some base ->
    let saved_b = c.breaks and saved_c = c.conts in
    c.breaks <- [];
    c.conts <- [];
    let outer = c.loop_depth in
    let end_st = in_loop c (fun () -> body st) in
    let check = function
      | None -> ()
      | Some s ->
        IS.iter
          (fun v ->
             let l = loc c v in
             if not (IS.mem v base) && l.loop_depth <= outer then
               error pos "%s 在循环里被移走，必须在本轮结束前重新赋值" l.lname)
          s
    in
    check end_st;
    List.iter check c.conts;
    let res = List.fold_left union st (end_st :: c.breaks) in
    c.breaks <- saved_b;
    c.conts <- saved_c;
    res

let rec expr c (st : IS.t option) (m : mode) (e : expr) : IS.t option =
  match st with
  | None -> None
  | Some s ->
    let pos = e.epos in
    match e.e with
    | Int _ | Bool _ | Str _ -> st
    | Interp ps -> List.fold_left (fun st p -> expr c st Reading p) st ps
    | Var x ->
      let l = loc c e.vid in
      if IS.mem e.vid s then error pos "%s 的值已经被移走，不能再使用" x;
      if m = Owning && not (is_copy e.ety) then begin
        if l.lkind <> LOwned then error pos "%s 是借用的，不能移走；需要副本请写 %s.copy()" x x;
        if IS.mem e.vid c.frozen then error pos "%s 正被 for 或 match 借用，不能移走" x;
        Some (IS.add e.vid s)
      end
      else st
    | Field (b, f) ->
      if m = Owning && not (is_copy e.ety) then error pos "不能把字段 %s 移出，请用 .copy()" f;
      expr c st Reading b
    | Index (b, i) ->
      if m = Owning && not (is_copy e.ety) then error pos "不能把列表元素移出，请用 .copy() 或 pop";
      expr c (expr c st Reading b) Reading i
    | Call _ | Method _ -> call c st e
    | List items -> List.fold_left (fun st x -> expr c st Owning x) st items
    | Unary (_, a) -> expr c st Reading a
    | Binary (_, a, b) -> expr c (expr c st Reading a) Reading b
    | If (cond, t, els) ->
      let st = expr c st Reading cond in
      let am = arm_mode m e.ety in
      let s1 = block c st am t in
      let s2 = match els with Some b -> block c st am b | None -> st in
      union s1 s2
    | Match (take, scrut, arms) ->
      let st = expr c st (if take then Owning else Reading) scrut in
      let r = if take then None else root scrut in
      with_frozen c r (fun () ->
          List.fold_left (fun acc (a : arm) -> union acc (expr c st (arm_mode m e.ety) a.body)) None arms)
    | Block b -> block c st (arm_mode m e.ety) b
    | Return eo ->
      ignore (match eo with Some x -> expr c st Owning x | None -> st);
      None
    | Break -> c.breaks <- st :: c.breaks; None
    | Continue -> c.conts <- st :: c.conts; None

and call c st e =
  let args = Check.full_args c.env e in
  let first = match args with a :: _ -> Some a.value.ety | [] -> None in
  let params, ret = Check.sig_of c.env e.epos e.resolved first in
  let is_ctor = Check.ctor_fields c.env e.resolved <> None in
  (* inout 参数的根变量：可写、未冻结，且不能同时出现在其它参数里 *)
  List.iteri
    (fun i a ->
       if a.amp then
         match root a.value with
         | None -> error a.value.epos "& 只能用于变量、字段或下标"
         | Some r ->
           let l = loc c r in
           if l.lkind = LRead then error a.value.epos "%s 是只读的，不能以 inout 传递" l.lname;
           if IS.mem r c.frozen then error a.value.epos "%s 正被 for 或 match 借用，不能修改" l.lname;
           List.iteri
             (fun j b ->
                if j <> i && IS.mem r (vars_of IS.empty b.value) then
                  error b.value.epos "%s 以 inout 传入的同时又被其它参数使用（违反排他性）" l.lname)
             args)
    args;
  (* 被移走的变量不能同时出现在其它参数里（C 的参数求值顺序不确定） *)
  List.iteri
    (fun i ((pm, _), a) ->
       match a.value.e with
       | Var x when (is_ctor || pm = Take) && not (is_copy a.value.ety) ->
         List.iteri
           (fun j b ->
              if j <> i && IS.mem a.value.vid (vars_of IS.empty b.value) then
                error b.value.epos "%s 被移走的同时又被其它参数使用" x)
           args
       | _ -> ())
    (List.combine params args);
  let st =
    List.fold_left2
      (fun st (pm, _) a ->
         let m = if is_ctor || pm = Take then Owning else Reading in
         expr c st m a.value)
      st params args
  in
  if ret = TNever then None else st

and block c st m (b : block) =
  let st = List.fold_left (stmt c) st b.stmts in
  match b.tail with Some e -> expr c st m e | None -> st

and stmt c st (s : stmt) =
  match st with
  | None -> None
  | Some _ ->
    match s.s with
    | SExpr e -> expr c st Discard e
    | SAssign (target, _, rhs, flag) ->
      let st = expr c st Owning rhs in
      if flag.is_decl then st
      else begin
        match st with
        | None -> None
        | Some sset ->
          match target.e with
          | Var x ->
            let l = loc c target.vid in
            if l.lkind = LRead then error s.spos "%s 是只读的，不能赋值" x;
            if IS.mem target.vid c.frozen then error s.spos "%s 正被 for 或 match 借用，不能赋值" x;
            Some (IS.remove target.vid sset)
          | _ ->
            (match root target with
             | None -> error s.spos "无效的赋值目标"
             | Some r ->
               let l = loc c r in
               if l.lkind = LRead then error s.spos "%s 是只读的，不能修改其内容" l.lname;
               if IS.mem r c.frozen then error s.spos "%s 正被 for 或 match 借用，不能修改" l.lname;
               if IS.mem r sset then error s.spos "%s 的值已经被移走" l.lname);
            (* 下标表达式本身按读取检查 *)
            let rec idx st t = match t.e with
              | Index (b, i) -> idx (expr c st Reading i) b
              | Field (b, _) -> idx st b
              | _ -> st
            in
            idx st target
      end
    | SForCond (cond, body) ->
      loop c s.spos st (fun st ->
          let st' = match cond with Some x -> expr c st Reading x | None -> st in
          block c st' Discard body)
    | SForRange (_, _, lo, hi, body) ->
      let st = expr c (expr c st Reading lo) Reading hi in
      loop c s.spos st (fun st -> block c st Discard body)
    | SForEach (_, _, it, body) ->
      let st = expr c st Reading it in
      with_frozen c (root it) (fun () -> loop c s.spos st (fun st -> block c st Discard body))

let check_fn env (f : fn_decl) =
  let c = { env; fn = f; loop_depth = 0; frozen = IS.empty; breaks = []; conts = [] } in
  let m = if f.ret = TUnit then Discard else Owning in
  ignore (block c (Some IS.empty) m f.body)

let check_program env items =
  List.iter (function IFn f -> check_fn env f | _ -> ()) items
