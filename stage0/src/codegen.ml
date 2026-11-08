(* C 代码生成：函数体。
   约定：
   - owned e：生成一个“新拥有”的值（调用方负责它的释放）；
   - read e：生成一个借来看的值，若需要临时变量，则登记到当前作用域，作用域结束时释放；
   - 移走变量 = 按位复制后把原变量清零，析构函数遇到零值什么都不做。 *)
open Ast
open Cgtypes

type scope = { mutable owned : (string * ty) list; is_loop : bool }

type g = {
  env : Check.env;
  fn : fn_decl;
  buf : Buffer.t;
  mutable ind : int;
  mutable scopes : scope list;
  ptrs : (int, unit) Hashtbl.t;     (* 通过指针访问的局部变量 *)
}

let lits = Buffer.create 1024
let lit_count = ref 0
let tmp_count = ref 0

let line g s =
  if s <> "" then begin
    Buffer.add_string g.buf (String.make (2 * g.ind) ' ');
    Buffer.add_string g.buf s;
    Buffer.add_char g.buf '\n'
  end

let linef g fmt = Printf.ksprintf (line g) fmt
let fresh pfx = incr tmp_count; Printf.sprintf "%s%d" pfx !tmp_count

let open_scope g is_loop = g.scopes <- { owned = []; is_loop } :: g.scopes
let drop_scope g sc = List.iter (fun (pl, t) -> line g (drop_stmt t pl)) sc.owned

let close_scope g =
  match g.scopes with
  | sc :: r -> drop_scope g sc; g.scopes <- r
  | [] -> failwith "内部错误：作用域栈为空"

let own g place t =
  if managed t then
    match g.scopes with
    | sc :: _ -> sc.owned <- (place, t) :: sc.owned
    | [] -> failwith "内部错误：作用域栈为空"

let drop_all g = List.iter (drop_scope g) g.scopes

let drop_to_loop g =
  let rec go = function
    | [] -> ()
    | sc :: r -> drop_scope g sc; if not sc.is_loop then go r
  in
  go g.scopes

let c_string s =
  let b = Buffer.create (String.length s + 2) in
  Buffer.add_char b '"';
  String.iter
    (fun c ->
       match c with
       | '"' -> Buffer.add_string b "\\\""
       | '\\' -> Buffer.add_string b "\\\\"
       | c when Char.code c >= 32 && Char.code c < 127 && c <> '?' -> Buffer.add_char b c
       | c -> Buffer.add_string b (Printf.sprintf "\\%03o" (Char.code c)))
    s;
  Buffer.add_char b '"';
  Buffer.contents b

let lit s =
  incr lit_count;
  Printf.bprintf lits "static lk_str lit%d;\n" !lit_count;
  Printf.sprintf "lk_lit(&lit%d, %s, %d)" !lit_count (c_string s) (String.length s)

let local g vid = Hashtbl.find g.fn.locals vid

let local_expr g vid =
  let l = local g vid in
  if Hashtbl.mem g.ptrs vid then "(*" ^ l.cname ^ ")" else l.cname

let opstr = function
  | Add -> "+" | Sub -> "-" | Mul -> "*" | Div -> "/" | Mod -> "%"
  | Eq -> "==" | Ne -> "!=" | Lt -> "<" | Le -> "<=" | Gt -> ">" | Ge -> ">="
  | And -> "&&" | Or -> "||"

let unit_like t = t = TUnit || t = TNever

(* if 条件：已经整体带括号就不再套一层，避免 clang 的 -Wparentheses-equality *)
let paren s =
  let n = String.length s in
  let wrapped =
    n >= 2 && s.[0] = '(' &&
    (let depth = ref 0 and closes_at = ref (-1) in
     String.iteri
       (fun i c ->
          if !closes_at < 0 then
            match c with
            | '(' -> incr depth
            | ')' -> decr depth; if !depth = 0 then closes_at := i
            | _ -> ())
       s;
     !closes_at = n - 1)
  in
  if wrapped then s else "(" ^ s ^ ")"

let rec place g e =
  match e.e with
  | Var _ -> local_expr g e.vid
  | Field (b, f) -> let rb = read g b in Printf.sprintf "%s.%s" rb (fld f)
  | Index (b, i) ->
    let rb = read g b in
    let ri = read g i in
    Printf.sprintf "(*lk_at_%s(&(%s), %s))" (mangle b.ety) rb ri
  | _ -> failwith "内部错误：不是位置表达式"

and read g e =
  register e.ety;
  if Check.is_place e then place g e
  else
    match e.e with
    | Str s -> lit s
    | _ when not (managed e.ety) -> owned g e
    | _ ->
      let v = owned g e in
      let t = fresh "t" in
      linef g "%s %s = %s;" (ctype e.ety) t v;
      own g t e.ety;
      t

and owned g e =
  register e.ety;
  match e.e with
  | Var _ | Field _ | Index _ ->
    let pl = place g e in
    if not (managed e.ety) then pl
    else if e.ety = TStr then "lk_str_dup(" ^ pl ^ ")"
    else (match e.e with
        | Var _ -> "LK_MOVE(" ^ pl ^ ")"
        | _ -> failwith "内部错误：从字段或下标移出")
  | Int n -> Printf.sprintf "INT64_C(%d)" n
  | Bool b -> if b then "true" else "false"
  | Str s -> lit s
  | Interp parts ->
    let t = fresh "t" in
    linef g "lk_str %s = lk_str_new();" t;
    List.iter
      (fun p ->
         let v = read g p in
         match p.ety with
         | TStr -> linef g "lk_str_append(&%s, %s);" t v
         | TInt -> linef g "lk_str_append_int(&%s, %s);" t v
         | TBool -> linef g "lk_str_append_bool(&%s, %s);" t v
         | _ -> ())
      parts;
    t
  | Call _ | Method _ -> call g e
  | List items ->
    let t = fresh "t" in
    linef g "%s %s = {0};" (ctype e.ety) t;
    List.iter (fun x -> let v = owned g x in linef g "lk_push_%s(&%s, %s);" (mangle e.ety) t v) items;
    t
  | Unary (Neg, a) -> "(-(" ^ read g a ^ "))"
  | Unary (Not, a) -> "(!(" ^ read g a ^ "))"
  | Binary (op, a, b) -> binary g op a b
  | If _ | Match _ | Block _ ->
    if unit_like e.ety then (control g e None; "")
    else begin
      let r = fresh "t" in
      linef g "%s %s = {0};" (ctype e.ety) r;
      control g e (Some r);
      r
    end
  | Return eo -> gen_return g eo; ""
  | Break -> drop_to_loop g; line g "break;"; ""
  | Continue -> drop_to_loop g; line g "continue;"; ""

and binary g op a b =
  match op with
  | And | Or ->
    let t = fresh "t" in
    let ra = read g a in
    linef g "bool %s = %s;" t ra;
    linef g "if (%s%s) {" (if op = And then "" else "!") t;
    g.ind <- g.ind + 1;
    open_scope g false;
    let rb = read g b in
    linef g "%s = %s;" t rb;
    close_scope g;
    g.ind <- g.ind - 1;
    line g "}";
    t
  | _ ->
    let ra = read g a in
    let rb = read g b in
    match op, a.ety with
    | Add, TStr -> Printf.sprintf "lk_str_cat(%s, %s)" ra rb
    | Eq, TStr -> Printf.sprintf "lk_str_eq(%s, %s)" ra rb
    | Ne, TStr -> Printf.sprintf "(!lk_str_eq(%s, %s))" ra rb
    | (Lt | Le | Gt | Ge), TStr -> Printf.sprintf "(lk_str_cmp(%s, %s) %s 0)" ra rb (opstr op)
    | Div, _ -> Printf.sprintf "lk_div(%s, %s)" ra rb
    | Mod, _ -> Printf.sprintf "lk_mod(%s, %s)" ra rb
    | _ -> Printf.sprintf "(%s %s %s)" ra (opstr op) rb

and call g e =
  let args = Check.full_args g.env e in
  let first = match args with a :: _ -> Some a.value.ety | [] -> None in
  let params, ret = Check.sig_of g.env e.epos e.resolved first in
  let ret_tmp v =
    if unit_like ret then (linef g "%s;" v; "")
    else begin
      let t = fresh "t" in
      linef g "%s %s = %s;" (ctype ret) t v;
      t
    end
  in
  let pass (m, pt) a =
    match m with
    | Take -> owned g a.value
    | Inout -> "&(" ^ place g a.value ^ ")"
    | Read -> if managed pt && pt <> TStr then "&(" ^ read g a.value ^ ")" else read g a.value
  in
  match e.resolved with
  | RStruct n ->
    let fs = Hashtbl.find g.env.Check.structs n in
    let vs = List.map (fun a -> owned g a.value) args in
    let inits = List.map2 (fun f v -> "." ^ fld f.fdname ^ " = " ^ v) fs vs in
    let t = fresh "t" in
    linef g "S_%s %s = { %s };" n t (if inits = [] then "0" else String.concat ", " inits);
    t
  | RVariant (en, i) ->
    let vs = List.map (fun a -> owned g a.value) args in
    ret_tmp (Printf.sprintf "lk_mk_%s_%d(%s)" (mangle (TEnum en)) i (String.concat ", " vs))
  | RFn f ->
    let vs = List.map2 pass params args in
    ret_tmp (fname f ^ "(" ^ String.concat ", " vs ^ ")")
  | RBuiltin b -> builtin g b args ret_tmp
  | RNone -> failwith "内部错误：未解析的调用"

and builtin g b args ret_tmp =
  let arg i = (List.nth args i).value in
  let rd i = read g (arg i) in
  let call1 f = let a = rd 0 in ret_tmp (Printf.sprintf "%s(%s)" f a) in
  match b with
  | "print" -> call1 "lk_print"
  | "eprint" -> call1 "lk_eprint"
  | "from_byte" -> call1 "lk_from_byte"
  | "int_str" -> call1 "lk_int_str"
  | "parse_int" -> call1 "lk_parse_int"
  | "read_file" -> call1 "lk_read_file"
  | "system" -> call1 "lk_system"
  | "exit" -> call1 "lk_exit"
  | "panic" -> call1 "lk_panic"
  | "len" ->
    let a = rd 0 in
    (match (arg 0).ety with
     | TStr -> ret_tmp (Printf.sprintf "lk_str_len(%s)" a)
     | _ -> ret_tmp (Printf.sprintf "(%s).len" a))
  | "byte_at" ->
    let s = rd 0 in
    let i = rd 1 in
    ret_tmp (Printf.sprintf "lk_byte_at(%s, %s)" s i)
  | "slice" ->
    let s = rd 0 in
    let a = rd 1 in
    let z = rd 2 in
    ret_tmp (Printf.sprintf "lk_slice(%s, %s, %s)" s a z)
  | "write_file" ->
    let p = rd 0 in
    let d = rd 1 in
    ret_tmp (Printf.sprintf "lk_write_file(%s, %s)" p d)
  | "join" ->
    let xs = rd 0 in
    let sep = rd 1 in
    ret_tmp (Printf.sprintf "lk_join_arr((%s).data, (%s).len, %s)" xs xs sep)
  | "args" ->
    let lt = TList TStr in
    let t = fresh "t" in
    linef g "%s %s = {0};" (ctype lt) t;
    linef g "for (int64_t i = 0; i < lk_argc(); i++) lk_push_%s(&%s, lk_argv(i));" (mangle lt) t;
    t
  | "push" ->
    let xs = place g (arg 0) in
    let v = owned g (arg 1) in
    ret_tmp (Printf.sprintf "lk_push_%s(&(%s), %s)" (mangle (arg 0).ety) xs v)
  | "replace" ->
    let pl = place g (arg 0) in
    let v = owned g (arg 1) in
    let t = fresh "t" in
    linef g "%s %s = %s; %s = %s;" (ctype (arg 0).ety) t pl pl v;
    t
  | "pop" ->
    let xs = place g (arg 0) in
    ret_tmp (Printf.sprintf "lk_pop_%s(&(%s))" (mangle (arg 0).ety) xs)
  | "copy" ->
    let a = rd 0 in
    ret_tmp (copy_expr (arg 0).ety a)
  | _ -> failwith ("内部错误：未知内置函数 " ^ b)

and gen_return g eo =
  match eo with
  | Some x when g.fn.ret <> TUnit ->
    let v = owned g x in
    if x.ety <> TNever then begin
      let r = fresh "r" in
      linef g "%s %s = %s;" (ctype g.fn.ret) r v;
      drop_all g;
      linef g "return %s;" r
    end
  | Some x -> discard g x; drop_all g; line g "return;"
  | None -> drop_all g; line g "return;"

(* 只为副作用求值，结果丢弃 *)
and discard g e =
  register e.ety;
  match e.e with
  | If _ | Match _ | Block _ -> control g e None
  | Int _ | Bool _ | Str _ -> ()
  | _ when Check.is_place e -> ()
  | _ ->
    let v = read g e in
    if v <> "" && not (managed e.ety) then linef g "(void)(%s);" v

and assign_into g target e =
  match target with
  | None -> discard g e
  | Some r ->
    let v = owned g e in
    if v <> "" && e.ety <> TNever then linef g "%s = %s;" r v

and block_into g (b : block) target =
  g.ind <- g.ind + 1;
  open_scope g false;
  List.iter (stmt g) b.stmts;
  (match b.tail with Some e -> assign_into g target e | None -> ());
  close_scope g;
  g.ind <- g.ind - 1

and control g e target =
  match e.e with
  | If (c, thn, els) ->
    let cv = read g c in
    linef g "if %s {" (paren cv);
    block_into g thn target;
    (match els with
     | Some b -> line g "} else {"; block_into g b target
     | None -> ());
    line g "}"
  | Block b -> line g "{"; block_into g b target; line g "}"
  | Match (take, s, arms) -> gen_match g take s arms target
  | _ -> failwith "内部错误：control"

and gen_match g take s arms target =
  let st = s.ety in
  let sv = fresh "m" in
  (match st with
   | TEnum _ when take -> let v = owned g s in linef g "%s %s = %s;" (ctype st) sv v
   | TEnum _ -> let v = read g s in linef g "%s* %s = &(%s);" (ctype st) sv v
   | _ -> let v = read g s in linef g "%s %s = %s;" (ctype st) sv v);
  let sval = match st with TEnum _ when not take -> "(*" ^ sv ^ ")" | _ -> sv in
  let drop_shell () = line g (drop_stmt st sv) in
  List.iteri
    (fun i (arm : arm) ->
       let cond =
         match arm.pat with
         | PWild | PBind _ -> "1"
         | PInt n -> Printf.sprintf "%s == INT64_C(%d)" sval n
         | PBool b -> Printf.sprintf "%s == %s" sval (if b then "true" else "false")
         | PVariant (vn, _) ->
           let _, idx = Hashtbl.find g.env.Check.variants vn in
           Printf.sprintf "%s->tag == %d" sval idx
       in
       linef g "%s (%s) {" (if i = 0 then "if" else "} else if") cond;
       g.ind <- g.ind + 1;
       open_scope g false;
       (match arm.pat with
        | PWild -> if take then drop_shell ()
        | PBind (_, b) ->
          let l = local g b.bvid in
          if take then begin
            linef g "%s %s = %s; %s = NULL;" (ctype st) l.cname sv sv;
            own g l.cname st
          end
          else begin
            linef g "%s* %s = &(%s);" (ctype st) l.cname sval;
            Hashtbl.replace g.ptrs b.bvid ()
          end
        | PInt _ | PBool _ -> ()
        | PVariant (vn, fields) ->
          let en, idx = Hashtbl.find g.env.Check.variants vn in
          let v = List.nth (Hashtbl.find g.env.Check.enums en) idx in
          List.iter2
            (fun pf fd ->
               match pf with
               | PFWild -> ()
               | PFBind (_, b) ->
                 let l = local g b.bvid in
                 let lv = Printf.sprintf "%s->u.v%d.%s" sval idx (fld fd.fdname) in
                 if take then begin
                   linef g "%s %s = %s; memset(&(%s), 0, sizeof(%s));" (ctype fd.fdty) l.cname lv lv l.cname;
                   own g l.cname fd.fdty
                 end
                 else begin
                   linef g "%s* %s = &(%s);" (ctype fd.fdty) l.cname lv;
                   Hashtbl.replace g.ptrs b.bvid ()
                 end)
            fields v.vfields;
          if take then drop_shell ());
       assign_into g target arm.body;
       close_scope g;
       g.ind <- g.ind - 1)
    arms;
  line g "} else {";
  line g "  lk_unreachable();";
  line g "}"

and stmt g (s : stmt) =
  match s.s with
  | SExpr e -> discard g e
  | SAssign (target, _, rhs, flag) ->
    if flag.is_decl then begin
      let l = local g target.vid in
      let v = owned g rhs in
      linef g "%s %s = %s;" (ctype l.lty) l.cname v;
      own g l.cname l.lty
    end
    else begin
      let t = target.ety in
      let v = owned g rhs in
      if managed t then begin
        let tmp = fresh "t" in
        linef g "%s %s = %s;" (ctype t) tmp v;
        let pl = place g target in
        line g (drop_stmt t pl);
        linef g "%s = %s;" pl tmp
      end
      else begin
        let pl = place g target in
        linef g "%s = %s;" pl v
      end
    end
  | SForCond (c, body) ->
    line g "for (;;) {";
    g.ind <- g.ind + 1;
    open_scope g true;
    (match c with
     | Some c ->
       let cv = read g c in
       linef g "if (!(%s)) {" cv;
       g.ind <- g.ind + 1;
       drop_scope g (List.hd g.scopes);
       line g "break;";
       g.ind <- g.ind - 1;
       line g "}"
     | None -> ());
    line g "{";
    block_into g body None;
    line g "}";
    close_scope g;
    g.ind <- g.ind - 1;
    line g "}"
  | SForRange (_, b, lo, hi, body) ->
    let l = local g b.bvid in
    let lv = read g lo in
    let lo_t = fresh "lo" in
    linef g "int64_t %s = %s;" lo_t lv;
    let hv = read g hi in
    let hi_t = fresh "hi" in
    linef g "int64_t %s = %s;" hi_t hv;
    linef g "for (int64_t %s = %s; %s < %s; %s++) {" l.cname lo_t l.cname hi_t l.cname;
    g.ind <- g.ind + 1;
    open_scope g true;
    line g "{";
    block_into g body None;
    line g "}";
    close_scope g;
    g.ind <- g.ind - 1;
    line g "}"
  | SForEach (_, b, it, body) ->
    let l = local g b.bvid in
    let iv = read g it in
    let lst = fresh "l" and i = fresh "i" in
    linef g "%s* %s = &(%s);" (ctype it.ety) lst iv;
    linef g "for (int64_t %s = 0; %s < %s->len; %s++) {" i i lst i;
    g.ind <- g.ind + 1;
    open_scope g true;
    linef g "%s* %s = &%s->data[%s];" (ctype l.lty) l.cname lst i;
    Hashtbl.replace g.ptrs b.bvid ();
    line g "{";
    block_into g body None;
    line g "}";
    close_scope g;
    g.ind <- g.ind - 1;
    line g "}"

let gen_fn env (f : fn_decl) : string * string =
  let g = { env; fn = f; buf = Buffer.create 4096; ind = 1; scopes = []; ptrs = Hashtbl.create 16 } in
  let ps =
    List.map
      (fun p ->
         let l = local g p.pvid in
         let by_ptr = match p.pmode with
           | Inout -> true
           | Read -> managed p.pty && p.pty <> TStr
           | Take -> false
         in
         if by_ptr then Hashtbl.replace g.ptrs p.pvid ();
         Printf.sprintf "%s%s %s" (ctype p.pty) (if by_ptr then "*" else "") l.cname)
      f.params
  in
  let header =
    Printf.sprintf "static %s %s(%s)" (ctype f.ret) (fname f.fname)
      (if ps = [] then "void" else String.concat ", " ps)
  in
  open_scope g false;
  List.iter (fun p -> if p.pmode = Take then own g (local g p.pvid).cname p.pty) f.params;
  if f.ret = TUnit then begin
    line g "{";
    block_into g f.body None;
    line g "}";
    close_scope g
  end
  else begin
    let r = fresh "r" in
    linef g "%s %s = {0};" (ctype f.ret) r;
    line g "{";
    block_into g f.body (Some r);
    line g "}";
    close_scope g;
    linef g "return %s;" r
  end;
  (header ^ ";\n", header ^ " {\n" ^ Buffer.contents g.buf ^ "}\n\n")

let gen_program env items : string =
  let fns = List.filter_map (function IFn f -> Some f | _ -> None) items in
  let parts = List.map (gen_fn env) fns in
  register (TList TStr);
  let types = emit_types env items in
  let b = Buffer.create 65536 in
  Buffer.add_string b "// 由 Lark stage0 生成，请勿手改\n#include \"lark_rt.h\"\n\n";
  Buffer.add_string b types;
  Buffer.add_string b "\n";
  List.iter (fun (p, _) -> Buffer.add_string b p) parts;
  Buffer.add_string b "\n";
  Buffer.add_buffer b lits;
  Buffer.add_string b "\n";
  List.iter (fun (_, d) -> Buffer.add_string b d) parts;
  Buffer.add_string b "int main(int argc, char** argv) { lk_init(argc, argv); f_main(); return 0; }\n";
  Buffer.contents b
