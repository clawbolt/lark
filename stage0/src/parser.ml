(* Lark0 语法分析：手写递归下降。 *)
open Ast
open Lexer

type st = { toks : (token * pos) array; mutable k : int }

let peek st = fst st.toks.(st.k)
let peek2 st = if st.k + 1 < Array.length st.toks then fst st.toks.(st.k + 1) else EOF
let pos st = snd st.toks.(st.k)
let advance st = if st.k < Array.length st.toks - 1 then st.k <- st.k + 1

let expect st t =
  if peek st = t then advance st
  else error (pos st) "期望 %s，实际是 %s" (show_token t) (show_token (peek st))

let accept st t = if peek st = t then (advance st; true) else false

let skip_seps st = while peek st = NEWLINE || peek st = SEMI || peek st = COMMA do advance st done
let skip_nl st = while peek st = NEWLINE do advance st done

let ident st =
  match peek st with
  | IDENT s -> advance st; s
  | t -> error (pos st) "期望标识符，实际是 %s" (show_token t)

let is_upper s = s <> "" && s.[0] >= 'A' && s.[0] <= 'Z'

let rec parse_type st =
  match peek st with
  | LBRACKET -> advance st; let t = parse_type st in expect st RBRACKET; TList t
  | IDENT "int" -> advance st; TInt
  | IDENT "bool" -> advance st; TBool
  | IDENT "str" -> advance st; TStr
  | IDENT s -> advance st; TNamed s
  | LPAREN -> advance st; expect st RPAREN; TUnit
  | t -> error (pos st) "期望类型，实际是 %s" (show_token t)

(* ---------- 表达式 ---------- *)

let rec parse_expr st = parse_or st

and parse_binary st next ops =
  let lhs = ref (next st) in
  let rec loop () =
    match List.assoc_opt (peek st) ops with
    | Some op ->
      let p = pos st in
      advance st;
      let rhs = next st in
      lhs := mk_expr p (Binary (op, !lhs, rhs));
      loop ()
    | None -> ()
  in
  loop ();
  !lhs

and parse_or st = parse_binary st parse_and [ OROR, Or ]
and parse_and st = parse_binary st parse_cmp [ ANDAND, And ]

and parse_cmp st =
  let lhs = parse_add st in
  let ops = [ EQEQ, Eq; NE, Ne; LT, Lt; LE, Le; GT, Gt; GE, Ge ] in
  match List.assoc_opt (peek st) ops with
  | Some op ->
    let p = pos st in
    advance st;
    let rhs = parse_add st in
    if List.mem_assoc (peek st) ops then error (pos st) "比较运算不能连写，请加括号";
    mk_expr p (Binary (op, lhs, rhs))
  | None -> lhs

and parse_add st = parse_binary st parse_mul [ PLUS, Add; MINUS, Sub ]
and parse_mul st = parse_binary st parse_unary [ STAR, Mul; SLASH, Div; PERCENT, Mod ]

and parse_unary st =
  let p = pos st in
  match peek st with
  | MINUS -> advance st; mk_expr p (Unary (Neg, parse_unary st))
  | BANG -> advance st; mk_expr p (Unary (Not, parse_unary st))
  | _ -> parse_postfix st

and parse_postfix st =
  let e = ref (parse_primary st) in
  let rec loop () =
    let p = pos st in
    match peek st with
    | DOT ->
      advance st;
      let name = ident st in
      if peek st = LPAREN then e := mk_expr p (Method (!e, name, parse_args st))
      else e := mk_expr p (Field (!e, name));
      loop ()
    | LBRACKET ->
      advance st;
      let idx = parse_expr st in
      expect st RBRACKET;
      e := mk_expr p (Index (!e, idx));
      loop ()
    | _ -> ()
  in
  loop ();
  !e

and parse_args st =
  expect st LPAREN;
  let args = ref [] in
  while peek st <> RPAREN do
    let label =
      match peek st, peek2 st with
      | IDENT l, COLON -> advance st; advance st; Some l
      | _ -> None
    in
    let amp = accept st AMP in
    let value = parse_expr st in
    args := { label; amp; value } :: !args;
    if peek st <> RPAREN then expect st COMMA
  done;
  expect st RPAREN;
  List.rev !args

and parse_interp p parts =
  let sub = function
    | IPLit s -> mk_expr p (Str s)
    | IPCode (code, cp) ->
      let st' = { toks = tokenize ~start:cp code; k = 0 } in
      skip_nl st';
      let e = parse_expr st' in
      skip_nl st';
      if peek st' <> EOF then error (pos st') "插值里只能写一个表达式";
      e
  in
  mk_expr p (Interp (List.map sub parts))

and parse_primary st =
  let p = pos st in
  match peek st with
  | INT n -> advance st; mk_expr p (Int n)
  | STR s -> advance st; mk_expr p (Str s)
  | INTERP parts -> advance st; parse_interp p parts
  | KW_TRUE -> advance st; mk_expr p (Bool true)
  | KW_FALSE -> advance st; mk_expr p (Bool false)
  | IDENT name ->
    advance st;
    if peek st = LPAREN then mk_expr p (Call (name, parse_args st))
    else if is_upper name then mk_expr p (Call (name, []))   (* 无字段的变体或结构体 *)
    else mk_expr p (Var name)
  | LPAREN ->
    advance st;
    let e = parse_expr st in
    expect st RPAREN;
    e
  | LBRACKET ->
    advance st;
    let items = ref [] in
    while peek st <> RBRACKET do
      items := parse_expr st :: !items;
      if peek st <> RBRACKET then expect st COMMA
    done;
    expect st RBRACKET;
    mk_expr p (List (List.rev !items))
  | LBRACE -> mk_expr p (Block (parse_block st))
  | KW_IF -> parse_if st
  | KW_MATCH -> parse_match st
  | KW_RETURN ->
    advance st;
    (match peek st with
     | NEWLINE | SEMI | RBRACE | COMMA | RPAREN -> mk_expr p (Return None)
     | _ -> mk_expr p (Return (Some (parse_expr st))))
  | KW_BREAK -> advance st; mk_expr p Break
  | KW_CONTINUE -> advance st; mk_expr p Continue
  | t -> error p "这里需要表达式，实际是 %s" (show_token t)

and parse_if st =
  let p = pos st in
  expect st KW_IF;
  let cond = parse_expr st in
  let thn = parse_block st in
  let els =
    if accept st KW_ELSE then
      if peek st = KW_IF then
        let e = parse_if st in
        Some { stmts = []; tail = Some e }
      else Some (parse_block st)
    else None
  in
  mk_expr p (If (cond, thn, els))

and parse_pattern st =
  let p = pos st in
  match peek st with
  | IDENT "_" -> advance st; PWild
  | IDENT s when is_upper s ->
    advance st;
    let fields =
      if accept st LPAREN then begin
        let fs = ref [] in
        while peek st <> RPAREN do
          (match peek st with
           | IDENT "_" -> advance st; fs := PFWild :: !fs
           | IDENT b when not (is_upper b) -> advance st; fs := PFBind (b, { bvid = -1 }) :: !fs
           | t -> error (pos st) "变体字段只能是小写名字或 _，实际是 %s" (show_token t));
          if peek st <> RPAREN then expect st COMMA
        done;
        expect st RPAREN;
        List.rev !fs
      end
      else []
    in
    PVariant (s, fields)
  | IDENT s -> advance st; PBind (s, { bvid = -1 })
  | INT n -> advance st; PInt n
  | MINUS -> advance st; (match peek st with INT n -> advance st; PInt (-n) | _ -> error p "期望整数")
  | KW_TRUE -> advance st; PBool true
  | KW_FALSE -> advance st; PBool false
  | t -> error p "无法识别的模式 %s" (show_token t)

and parse_match st =
  let p = pos st in
  expect st KW_MATCH;
  let take = accept st KW_TAKE in
  let scrut = parse_expr st in
  expect st LBRACE;
  skip_seps st;
  let arms = ref [] in
  while peek st <> RBRACE do
    let ppos = pos st in
    let pat = parse_pattern st in
    expect st FATARROW;
    let body = parse_expr st in
    arms := { pat; ppos; body } :: !arms;
    if peek st <> RBRACE then (match peek st with
        | NEWLINE | SEMI | COMMA -> skip_seps st
        | t -> error (pos st) "分支之间需要换行或逗号，实际是 %s" (show_token t))
  done;
  expect st RBRACE;
  mk_expr p (Match (take, scrut, List.rev !arms))

(* ---------- 语句与块 ---------- *)

and parse_stmt st =
  let p = pos st in
  match peek st with
  | KW_FOR -> parse_for st
  | _ ->
    let e = parse_expr st in
    (match peek st, e.e with
     | COLON, Var _ ->
       advance st;
       let t = parse_type st in
       expect st EQ;
       let rhs = parse_expr st in
       { s = SAssign (e, Some t, rhs, { is_decl = false }); spos = p }
     | EQ, _ ->
       advance st;
       let rhs = parse_expr st in
       { s = SAssign (e, None, rhs, { is_decl = false }); spos = p }
     | (PLUSEQ | MINUSEQ | STAREQ) as t, _ ->
       advance st;
       let op = match t with PLUSEQ -> Add | MINUSEQ -> Sub | _ -> Mul in
       let rhs = parse_expr st in
       { s = SAssign (e, None, mk_expr p (Binary (op, e, rhs)), { is_decl = false }); spos = p }
     | _ -> { s = SExpr e; spos = p })

and parse_for st =
  let p = pos st in
  expect st KW_FOR;
  match peek st, peek2 st with
  | LBRACE, _ -> { s = SForCond (None, parse_block st); spos = p }
  | IDENT x, KW_IN ->
    advance st; advance st;
    let a = parse_expr st in
    if accept st DOTDOT then begin
      let b = parse_expr st in
      { s = SForRange (x, { bvid = -1 }, a, b, parse_block st); spos = p }
    end
    else { s = SForEach (x, { bvid = -1 }, a, parse_block st); spos = p }
  | _ ->
    let c = parse_expr st in
    { s = SForCond (Some c, parse_block st); spos = p }

and parse_block st =
  expect st LBRACE;
  skip_nl st;
  let stmts = ref [] in
  while peek st <> RBRACE do
    stmts := parse_stmt st :: !stmts;
    (match peek st with
     | NEWLINE | SEMI -> while peek st = NEWLINE || peek st = SEMI do advance st done
     | RBRACE -> ()
     | t -> error (pos st) "语句之后需要换行，实际是 %s" (show_token t))
  done;
  expect st RBRACE;
  match !stmts with
  | { s = SExpr e; _ } :: rest -> { stmts = List.rev rest; tail = Some e }
  | l -> { stmts = List.rev l; tail = None }

(* ---------- 顶层 ---------- *)

let parse_fields st =
  expect st LBRACE;
  skip_seps st;
  let fs = ref [] in
  while peek st <> RBRACE do
    let n = ident st in
    expect st COLON;
    let t = parse_type st in
    fs := { fdname = n; fdty = t } :: !fs;
    skip_seps st
  done;
  expect st RBRACE;
  List.rev !fs

let parse_variant_fields st =
  if not (accept st LPAREN) then []
  else begin
    let fs = ref [] and i = ref 0 in
    while peek st <> RPAREN do
      let name =
        match peek st, peek2 st with
        | IDENT n, COLON -> advance st; advance st; n
        | _ -> "_" ^ string_of_int !i
      in
      fs := { fdname = name; fdty = parse_type st } :: !fs;
      incr i;
      if peek st <> RPAREN then expect st COMMA
    done;
    expect st RPAREN;
    List.rev !fs
  end

let parse_item st =
  let p = pos st in
  match peek st with
  | KW_TYPE ->
    advance st;
    let n = ident st in
    IStruct (n, parse_fields st, p)
  | KW_ENUM ->
    advance st;
    let n = ident st in
    expect st LBRACE;
    skip_seps st;
    let vs = ref [] in
    while peek st <> RBRACE do
      let vn = ident st in
      if not (is_upper vn) then error (pos st) "变体名必须大写开头：%s" vn;
      vs := { vname = vn; vfields = parse_variant_fields st } :: !vs;
      skip_seps st
    done;
    expect st RBRACE;
    IEnum (n, List.rev !vs, p)
  | KW_FN ->
    advance st;
    let name = ident st in
    expect st LPAREN;
    let ps = ref [] in
    while peek st <> RPAREN do
      let pp = pos st in
      let pmode = if accept st KW_INOUT then Inout else if accept st KW_TAKE then Take else Read in
      let pname = ident st in
      expect st COLON;
      let pty = parse_type st in
      ps := { pname; pmode; pty; ppos_ = pp; pvid = -1 } :: !ps;
      if peek st <> RPAREN then expect st COMMA
    done;
    expect st RPAREN;
    let ret = if accept st ARROW then parse_type st else TUnit in
    let body = parse_block st in
    IFn { fname = name; params = List.rev !ps; ret; body; fpos = p; locals = Hashtbl.create 16 }
  | t -> error p "顶层只能是 fn / type / enum，实际是 %s" (show_token t)

let parse_program (src : string) : item list =
  let st = { toks = tokenize src; k = 0 } in
  let items = ref [] in
  skip_nl st;
  while peek st <> EOF do
    items := parse_item st :: !items;
    skip_nl st
  done;
  List.rev !items
