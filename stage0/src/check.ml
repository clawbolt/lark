(* Lark0 类型检查：解析名字、回填类型、为局部变量分配编号。 *)
open Ast

type env = {
  structs : (string, field list) Hashtbl.t;
  enums : (string, variant list) Hashtbl.t;
  variants : (string, string * int) Hashtbl.t;
  fns : (string, fn_decl) Hashtbl.t;
}

let builtin_names = [
  "print"; "eprint"; "len"; "byte_at"; "slice"; "from_byte"; "int_str"; "parse_int";
  "read_file"; "write_file"; "args"; "exit"; "panic"; "push"; "pop"; "copy"; "join"; "system"; "replace";
]

let rec resolve_ty env pos = function
  | TNamed n ->
    if Hashtbl.mem env.structs n then TStruct n
    else if Hashtbl.mem env.enums n then TEnum n
    else error pos "未知类型 %s" n
  | TList t -> TList (resolve_ty env pos t)
  | t -> t

(* 内置函数与普通函数的签名。泛型内置函数需要第一个参数的类型。 *)
let sig_of env pos (r : resolved) (first : ty option) : (mode * ty) list * ty =
  let need_first () = match first with Some t -> t | None -> error pos "缺少参数" in
  match r with
  | RFn n ->
    let f = Hashtbl.find env.fns n in
    (List.map (fun p -> (p.pmode, p.pty)) f.params, f.ret)
  | RStruct n -> (List.map (fun f -> (Take, f.fdty)) (Hashtbl.find env.structs n), TStruct n)
  | RVariant (en, i) ->
    let v = List.nth (Hashtbl.find env.enums en) i in
    (List.map (fun f -> (Take, f.fdty)) v.vfields, TEnum en)
  | RNone -> error pos "未解析的调用"
  | RBuiltin b ->
    match b with
    | "print" | "eprint" -> ([ Read, TStr ], TUnit)
    | "byte_at" -> ([ Read, TStr; Read, TInt ], TInt)
    | "slice" -> ([ Read, TStr; Read, TInt; Read, TInt ], TStr)
    | "from_byte" -> ([ Read, TInt ], TStr)
    | "int_str" -> ([ Read, TInt ], TStr)
    | "parse_int" -> ([ Read, TStr ], TInt)
    | "read_file" -> ([ Read, TStr ], TStr)
    | "write_file" -> ([ Read, TStr; Read, TStr ], TUnit)
    | "args" -> ([], TList TStr)
    | "exit" -> ([ Read, TInt ], TNever)
    | "panic" -> ([ Read, TStr ], TNever)
    | "join" -> ([ Read, TList TStr; Read, TStr ], TStr)
    | "system" -> ([ Read, TStr ], TInt)
    | "len" ->
      (match need_first () with
       | (TStr | TList _) as t -> ([ Read, t ], TInt)
       | t -> error pos "len 只能用于 str 或列表，而不是 %s" (show_ty t))
    | "copy" -> let t = need_first () in ([ Read, t ], t)
    | "push" ->
      (match need_first () with
       | TList t as lt -> ([ Inout, lt; Take, t ], TUnit)
       | t -> error pos "push 的第一个参数必须是列表，而不是 %s" (show_ty t))
    | "replace" -> let t = need_first () in ([ Inout, t; Take, t ], t)
    | "pop" ->
      (match need_first () with
       | TList t as lt -> ([ Inout, lt ], t)
       | t -> error pos "pop 的参数必须是列表，而不是 %s" (show_ty t))
    | _ -> error pos "未知内置函数 %s" b

let is_generic_builtin = function
  | RBuiltin ("len" | "copy" | "push" | "pop" | "replace") -> true
  | _ -> false

(* 结构体 / 变体构造：按字段顺序整理参数 *)
let order_args pos (fields : field list) (args : arg list) : arg list =
  let labeled = List.exists (fun a -> a.label <> None) args in
  if List.length args <> List.length fields then
    error pos "需要 %d 个字段，给了 %d 个" (List.length fields) (List.length args);
  if not labeled then args
  else
    List.map
      (fun f ->
         match List.filter (fun a -> a.label = Some f.fdname) args with
         | [ a ] -> a
         | [] -> error pos "缺少字段 %s" f.fdname
         | _ -> error pos "字段 %s 重复" f.fdname)
      fields

let ctor_fields env = function
  | RStruct n -> Some (Hashtbl.find env.structs n)
  | RVariant (en, i) -> Some (List.nth (Hashtbl.find env.enums en) i).vfields
  | _ -> None

(* 调用的完整参数表（方法调用把接收者放在最前面）。供后续阶段使用。 *)
let full_args env (e : expr) : arg list =
  match e.e with
  | Call (_, args) ->
    (match ctor_fields env e.resolved with
     | Some fs -> order_args e.epos fs args
     | None -> args)
  | Method (recv, _, args) ->
    let params, _ = sig_of env e.epos e.resolved (Some recv.ety) in
    let amp = match params with (Inout, _) :: _ -> true | _ -> false in
    { label = None; amp; value = recv } :: args
  | _ -> []

type fctx = {
  env : env;
  fn : fn_decl;
  mutable scopes : (string, int) Hashtbl.t list;
  mutable loop_depth : int;
}

let counter = ref 0

let lookup fc name =
  let rec go = function
    | [] -> None
    | s :: r -> (match Hashtbl.find_opt s name with Some v -> Some v | None -> go r)
  in
  go fc.scopes

let declare fc pos name ty kind =
  if lookup fc name <> None then error pos "变量 %s 已存在（Lark 不允许遮蔽）" name;
  incr counter;
  let vid = !counter in
  Hashtbl.replace fc.fn.locals vid
    { lname = name; cname = Printf.sprintf "v_%s_%d" name vid; lty = ty; lkind = kind;
      loop_depth = fc.loop_depth };
  Hashtbl.replace (List.hd fc.scopes) name vid;
  vid

let push_scope fc = fc.scopes <- Hashtbl.create 8 :: fc.scopes
let pop_scope fc = fc.scopes <- List.tl fc.scopes

let local fc vid = Hashtbl.find fc.fn.locals vid

let join pos a b =
  match a, b with
  | TNever, t | t, TNever -> t
  | a, b when a = b -> a
  | a, b -> error pos "分支类型不一致：%s 与 %s" (show_ty a) (show_ty b)

let expect_ty pos want got =
  if got <> TNever && want <> got then
    error pos "类型不匹配：需要 %s，实际是 %s" (show_ty want) (show_ty got)

let rec is_place e = match e.e with
  | Var _ -> true
  | Field (b, _) | Index (b, _) -> is_place b
  | _ -> false

let rec check_expr fc (expect : ty option) (e : expr) : ty =
  let t = check_expr_ fc expect e in
  e.ety <- t;
  t

and check_expr_ fc expect e =
  let pos = e.epos in
  match e.e with
  | Int _ -> TInt
  | Bool _ -> TBool
  | Str _ -> TStr
  | Interp parts ->
    List.iter
      (fun p ->
         match check_expr fc None p with
         | TInt | TBool | TStr -> ()
         | t -> error p.epos "插值只支持 int / bool / str，而不是 %s" (show_ty t))
      parts;
    TStr
  | Var x ->
    (match lookup fc x with
     | Some vid -> e.vid <- vid; (local fc vid).lty
     | None -> error pos "未定义的变量 %s" x)
  | Field (b, f) ->
    (match check_expr fc None b with
     | TStruct s ->
       (match List.find_opt (fun fd -> fd.fdname = f) (Hashtbl.find fc.env.structs s) with
        | Some fd -> fd.fdty
        | None -> error pos "%s 没有字段 %s" s f)
     | t -> error pos "%s 不是结构体，不能访问字段 %s" (show_ty t) f)
  | Index (b, i) ->
    let tb = check_expr fc None b in
    expect_ty i.epos TInt (check_expr fc (Some TInt) i);
    (match tb with TList t -> t | t -> error pos "%s 不能下标访问" (show_ty t))
  | Call (name, args) -> check_call fc pos e name None args
  | Method (recv, name, args) -> check_call fc pos e name (Some recv) args
  | List [] ->
    (match expect with
     | Some (TList _ as t) -> t
     | _ -> error pos "空列表需要类型标注，例如 xs: [int] = []")
  | List (first :: rest) ->
    let want = match expect with Some (TList t) -> Some t | _ -> None in
    let t = check_expr fc want first in
    List.iter (fun x -> expect_ty x.epos t (check_expr fc (Some t) x)) rest;
    TList t
  | Unary (Neg, a) -> expect_ty pos TInt (check_expr fc (Some TInt) a); TInt
  | Unary (Not, a) -> expect_ty pos TBool (check_expr fc (Some TBool) a); TBool
  | Binary (op, a, b) ->
    let ta = check_expr fc None a in
    let tb = check_expr fc (Some ta) b in
    if ta <> tb && ta <> TNever && tb <> TNever then
      error pos "运算两侧类型不同：%s 与 %s" (show_ty ta) (show_ty tb);
    (match op, ta with
     | Add, (TInt | TStr) -> ta
     | (Sub | Mul | Div | Mod), TInt -> TInt
     | (Eq | Ne), (TInt | TBool | TStr) -> TBool
     | (Lt | Le | Gt | Ge), (TInt | TStr) -> TBool
     | (And | Or), TBool -> TBool
     | _ -> error pos "运算不支持类型 %s" (show_ty ta))
  | If (c, thn, els) ->
    expect_ty c.epos TBool (check_expr fc (Some TBool) c);
    let tt = check_block fc expect thn in
    (match els with
     | None -> TUnit
     | Some b -> join pos tt (check_block fc expect b))
  | Match (take, scrut, arms) -> check_match fc expect pos take scrut arms
  | Block b -> check_block fc expect b
  | Return eo ->
    (match eo with
     | None -> if fc.fn.ret <> TUnit then error pos "需要返回 %s" (show_ty fc.fn.ret)
     | Some x -> expect_ty x.epos fc.fn.ret (check_expr fc (Some fc.fn.ret) x));
    TNever
  | Break | Continue ->
    if fc.loop_depth = 0 then error pos "break / continue 只能在循环里使用";
    TNever

and check_call fc pos e name recv args =
  let env = fc.env in
  let r =
    if Hashtbl.mem env.structs name then RStruct name
    else if Hashtbl.mem env.variants name then (let en, i = Hashtbl.find env.variants name in RVariant (en, i))
    else if Hashtbl.mem env.fns name then RFn name
    else if List.mem name builtin_names then RBuiltin name
    else error pos "未定义的函数 %s" name
  in
  e.resolved <- r;
  (match r, recv with
   | (RStruct _ | RVariant _), Some _ -> error pos "%s 不能用方法语法调用" name
   | _ -> ());
  let ctor = ctor_fields env r in
  (match ctor with
   | None -> List.iter (fun a -> if a.label <> None then error pos "函数参数不能带名字") args
   | Some _ -> List.iter (fun a -> if a.amp then error pos "构造时不能写 &") args);
  (* 先检查第一个参数（泛型内置函数靠它推断签名） *)
  let first_expr = match recv, args with
    | Some r, _ -> Some r
    | None, a :: _ when ctor = None -> Some a.value
    | _ -> None
  in
  let first_ty =
    match first_expr with
    | Some fe when is_generic_builtin r || recv <> None -> Some (check_expr fc None fe)
    | _ -> None
  in
  let params, ret = sig_of env pos r first_ty in
  let all_args =
    match recv with
    | Some rv ->
      let amp = match params with (Inout, _) :: _ -> true | _ -> false in
      { label = None; amp; value = rv } :: args
    | None -> (match ctor with Some fs -> order_args pos fs args | None -> args)
  in
  if List.length all_args <> List.length params then
    error pos "%s 需要 %d 个参数，给了 %d 个" name (List.length params) (List.length all_args);
  List.iteri
    (fun i ((m, pt), a) ->
       let already = i = 0 && first_ty <> None in
       let t = if already then a.value.ety else check_expr fc (Some pt) a.value in
       expect_ty a.value.epos pt t;
       if ctor = None then begin
         if m = Inout && not a.amp then error a.value.epos "inout 参数需要写成 &x";
         if m <> Inout && a.amp then error a.value.epos "只有 inout 参数可以写 &";
         if m = Inout && not (is_place a.value) then error a.value.epos "& 只能用于变量、字段或下标"
       end)
    (List.combine params all_args);
  ret

and bind_pattern fc take pos (t : ty) (pat : pattern) =
  let kind = if take then LOwned else LRead in
  match pat with
  | PWild -> ()
  | PBind (x, b) -> b.bvid <- declare fc pos x t kind
  | PInt _ -> if t <> TInt then error pos "整数模式不能匹配 %s" (show_ty t)
  | PBool _ -> if t <> TBool then error pos "布尔模式不能匹配 %s" (show_ty t)
  | PVariant (vn, fields) ->
    (match t with
     | TEnum en ->
       (match Hashtbl.find_opt fc.env.variants vn with
        | Some (en', i) when en' = en ->
          let v = List.nth (Hashtbl.find fc.env.enums en) i in
          if List.length fields <> List.length v.vfields then
            error pos "变体 %s 有 %d 个字段，模式写了 %d 个" vn (List.length v.vfields) (List.length fields);
          List.iter2
            (fun pf fd ->
               match pf with
               | PFWild -> ()
               | PFBind (x, b) -> b.bvid <- declare fc pos x fd.fdty kind)
            fields v.vfields
        | _ -> error pos "%s 不是 %s 的变体" vn en)
     | _ -> error pos "变体模式不能匹配 %s" (show_ty t))

and check_match fc expect pos take scrut arms =
  let ts = check_expr fc None scrut in
  if take then (match ts with TEnum _ -> () | _ -> error pos "match take 只能用于枚举");
  (match ts with
   | TEnum _ | TInt | TBool -> ()
   | t -> error pos "match 不支持 %s（字符串请用 if）" (show_ty t));
  if arms = [] then error pos "match 至少需要一个分支";
  let result = ref TNever in
  List.iter
    (fun (arm : arm) ->
       push_scope fc;
       bind_pattern fc take arm.ppos ts arm.pat;
       let t = check_expr fc expect arm.body in
       result := join arm.body.epos !result t;
       pop_scope fc)
    arms;
  (* 穷尽检查 *)
  let catch_all = List.exists (fun a -> match a.pat with PWild | PBind _ -> true | _ -> false) arms in
  if not catch_all then begin
    match ts with
    | TEnum en ->
      List.iter
        (fun v ->
           if not (List.exists (fun a -> match a.pat with PVariant (n, _) -> n = v.vname | _ -> false) arms)
           then error pos "match 没有覆盖变体 %s" v.vname)
        (Hashtbl.find fc.env.enums en)
    | TBool ->
      let has b = List.exists (fun a -> a.pat = PBool b) arms in
      if not (has true && has false) then error pos "match 没有覆盖所有布尔值"
    | _ -> error pos "整数 match 需要 _ 分支"
  end;
  !result

and check_block fc expect (b : block) : ty =
  push_scope fc;
  List.iter (check_stmt fc) b.stmts;
  let t = match b.tail with Some e -> check_expr fc expect e | None -> TUnit in
  pop_scope fc;
  t

and check_stmt fc (s : stmt) =
  match s.s with
  | SExpr e -> ignore (check_expr fc None e)
  | SAssign (target, annot, rhs, flag) ->
    (match target.e, annot with
     | Var x, _ when lookup fc x = None ->
       let t =
         match annot with
         | Some a ->
           let a = resolve_ty fc.env s.spos a in
           expect_ty rhs.epos a (check_expr fc (Some a) rhs);
           a
         | None ->
           let t = check_expr fc None rhs in
           if t = TNever || t = TUnit then error s.spos "不能把 %s 赋给变量" (show_ty t);
           t
       in
       flag.is_decl <- true;
       target.vid <- declare fc s.spos x t LOwned;
       target.ety <- t
     | _, Some _ -> error s.spos "变量已经声明过，不能再标注类型"
     | _, None ->
       if not (is_place target) then error s.spos "只能给变量、字段或下标赋值";
       let t = check_expr fc None target in
       expect_ty rhs.epos t (check_expr fc (Some t) rhs))
  | SForCond (c, body) ->
    (match c with Some c -> expect_ty c.epos TBool (check_expr fc (Some TBool) c) | None -> ());
    fc.loop_depth <- fc.loop_depth + 1;
    ignore (check_block fc None body);
    fc.loop_depth <- fc.loop_depth - 1
  | SForRange (x, b, lo, hi, body) ->
    expect_ty lo.epos TInt (check_expr fc (Some TInt) lo);
    expect_ty hi.epos TInt (check_expr fc (Some TInt) hi);
    fc.loop_depth <- fc.loop_depth + 1;
    push_scope fc;
    b.bvid <- declare fc s.spos x TInt LOwned;
    ignore (check_block fc None body);
    pop_scope fc;
    fc.loop_depth <- fc.loop_depth - 1
  | SForEach (x, b, it, body) ->
    let elt = match check_expr fc None it with
      | TList t -> t
      | t -> error it.epos "for in 需要列表，而不是 %s" (show_ty t)
    in
    fc.loop_depth <- fc.loop_depth + 1;
    push_scope fc;
    b.bvid <- declare fc s.spos x elt LRead;
    ignore (check_block fc None body);
    pop_scope fc;
    fc.loop_depth <- fc.loop_depth - 1

let check_fn env (f : fn_decl) =
  let fc = { env; fn = f; scopes = [ Hashtbl.create 8 ]; loop_depth = 0 } in
  List.iter
    (fun p ->
       let kind = match p.pmode with Take -> LOwned | Read -> LRead | Inout -> LInout in
       p.pvid <- declare fc p.ppos_ p.pname p.pty kind)
    f.params;
  let t = check_block fc (Some f.ret) f.body in
  if f.ret <> TUnit then expect_ty f.fpos f.ret t

(* 收集声明、解析类型，返回类型已解析的条目 *)
let check_program (items : item list) : env * item list =
  let env = { structs = Hashtbl.create 16; enums = Hashtbl.create 16;
              variants = Hashtbl.create 64; fns = Hashtbl.create 64 } in
  let taken = Hashtbl.create 64 in
  let claim pos n =
    if Hashtbl.mem taken n || List.mem n builtin_names then error pos "名字 %s 重复定义" n;
    Hashtbl.replace taken n ()
  in
  List.iter
    (function
      | IStruct (n, fs, p) -> claim p n; Hashtbl.replace env.structs n fs
      | IEnum (n, vs, p) ->
        claim p n;
        Hashtbl.replace env.enums n vs;
        List.iteri (fun i v -> claim p v.vname; Hashtbl.replace env.variants v.vname (n, i)) vs
      | IFn f -> claim f.fpos f.fname)
    items;
  let rfields p fs =
    let seen = Hashtbl.create 8 in
    List.map
      (fun f ->
         if Hashtbl.mem seen f.fdname then error p "字段 %s 重复" f.fdname;
         Hashtbl.replace seen f.fdname ();
         { f with fdty = resolve_ty env p f.fdty })
      fs
  in
  let items =
    List.map
      (function
        | IStruct (n, fs, p) ->
          let fs = rfields p fs in
          Hashtbl.replace env.structs n fs;
          IStruct (n, fs, p)
        | IEnum (n, vs, p) ->
          let vs = List.map (fun v -> { v with vfields = rfields p v.vfields }) vs in
          Hashtbl.replace env.enums n vs;
          IEnum (n, vs, p)
        | IFn f ->
          let f = { f with
                    params = List.map (fun p -> { p with pty = resolve_ty env p.ppos_ p.pty }) f.params;
                    ret = resolve_ty env f.fpos f.ret } in
          Hashtbl.replace env.fns f.fname f;
          IFn f)
      items
  in
  (match Hashtbl.find_opt env.fns "main" with
   | Some m -> if m.params <> [] || m.ret <> TUnit then error m.fpos "main 不能有参数或返回值"
   | None -> error dummy_pos "缺少 fn main()");
  List.iter (function IFn f -> check_fn env f | _ -> ()) items;
  (env, items)
