(* Lark0 词法分析。换行在 { } 内或顶层有意义，在 ( ) [ ] 内忽略。 *)
open Ast

type interp_part = IPLit of string | IPCode of string * pos

type token =
  | IDENT of string
  | INT of int
  | STR of string
  | INTERP of interp_part list
  | KW_FN | KW_TYPE | KW_ENUM | KW_IF | KW_ELSE | KW_MATCH | KW_FOR | KW_IN
  | KW_RETURN | KW_BREAK | KW_CONTINUE | KW_TRUE | KW_FALSE | KW_TAKE | KW_INOUT
  | LPAREN | RPAREN | LBRACE | RBRACE | LBRACKET | RBRACKET
  | COMMA | COLON | SEMI | DOT | DOTDOT | ARROW | FATARROW | AMP
  | PLUS | MINUS | STAR | SLASH | PERCENT
  | EQEQ | NE | LT | LE | GT | GE | ANDAND | OROR | BANG
  | EQ | PLUSEQ | MINUSEQ | STAREQ
  | NEWLINE
  | EOF

let keywords = [
  "fn", KW_FN; "type", KW_TYPE; "enum", KW_ENUM; "if", KW_IF; "else", KW_ELSE;
  "match", KW_MATCH; "for", KW_FOR; "in", KW_IN; "return", KW_RETURN;
  "break", KW_BREAK; "continue", KW_CONTINUE; "true", KW_TRUE; "false", KW_FALSE;
  "take", KW_TAKE; "inout", KW_INOUT;
]

let show_token = function
  | IDENT s -> s
  | INT n -> string_of_int n
  | STR _ | INTERP _ -> "字符串"
  | NEWLINE -> "换行"
  | EOF -> "文件结尾"
  | LPAREN -> "(" | RPAREN -> ")" | LBRACE -> "{" | RBRACE -> "}"
  | LBRACKET -> "[" | RBRACKET -> "]" | COMMA -> "," | COLON -> ":" | SEMI -> ";"
  | DOT -> "." | DOTDOT -> ".." | ARROW -> "->" | FATARROW -> "=>" | AMP -> "&"
  | EQ -> "=" | PLUSEQ -> "+=" | MINUSEQ -> "-=" | STAREQ -> "*="
  | t ->
    (match List.find_opt (fun (_, k) -> k = t) keywords with
     | Some (s, _) -> s
     | None -> "运算符")

(* 这些 token 之后的换行视为续行 *)
let continues = function
  | PLUS | MINUS | STAR | SLASH | PERCENT | EQEQ | NE | LT | LE | GT | GE
  | ANDAND | OROR | BANG | EQ | PLUSEQ | MINUSEQ | STAREQ | COMMA | DOT | DOTDOT
  | ARROW | FATARROW | AMP | COLON | LPAREN | LBRACKET | LBRACE | NEWLINE -> true
  | _ -> false

let is_ident_start c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c = '_'
let is_digit c = c >= '0' && c <= '9'
let is_ident_char c = is_ident_start c || is_digit c

let tokenize ?(start = { line = 1; col = 1 }) (src : string) : (token * pos) array =
  let n = String.length src in
  let i = ref 0 and line = ref start.line and col = ref start.col in
  let toks = ref [] in
  let stack = ref [] in               (* 括号栈 *)
  let last = ref NEWLINE in
  let push t p = toks := (t, p) :: !toks; last := t in
  let peek k = if !i + k < n then src.[!i + k] else '\000' in
  let adv () =
    if src.[!i] = '\n' then (incr line; col := 1) else incr col;
    incr i
  in
  let newline_significant () = match !stack with [] | '{' :: _ -> true | _ -> false in
  (* 下一行是否以 . 开头（方法链续行） *)
  let next_line_starts_with_dot () =
    let j = ref !i in
    while !j < n && (src.[!j] = ' ' || src.[!j] = '\t' || src.[!j] = '\n' || src.[!j] = '\r') do incr j done;
    !j + 1 < n && src.[!j] = '.' && src.[!j + 1] <> '.'
  in
  let read_escape p =
    adv ();
    if !i >= n then error p "字符串未结束";
    let c = src.[!i] in
    adv ();
    match c with
    | 'n' -> '\n' | 't' -> '\t' | 'r' -> '\r' | '0' -> '\000'
    | '\\' -> '\\' | '"' -> '"' | '\'' -> '\'' | '#' -> '#'
    | _ -> error p "未知转义 \\%c" c
  in
  while !i < n do
    let c = src.[!i] in
    let p = { line = !line; col = !col } in
    if c = '\n' then begin
      adv ();
      if newline_significant () && not (continues !last) && not (next_line_starts_with_dot ())
      then push NEWLINE p
    end
    else if c = ' ' || c = '\t' || c = '\r' then adv ()
    else if c = '/' && peek 1 = '/' then
      while !i < n && src.[!i] <> '\n' do adv () done
    else if is_ident_start c then begin
      let b = !i in
      while !i < n && is_ident_char src.[!i] do adv () done;
      let s = String.sub src b (!i - b) in
      push (match List.assoc_opt s keywords with Some k -> k | None -> IDENT s) p
    end
    else if is_digit c then begin
      let b = !i in
      while !i < n && (is_digit src.[!i] || src.[!i] = '_') do adv () done;
      let s = String.concat "" (String.split_on_char '_' (String.sub src b (!i - b))) in
      push (INT (int_of_string s)) p
    end
    else if c = '\'' then begin
      adv ();
      if !i >= n then error p "字符字面量未结束";
      let ch = if src.[!i] = '\\' then read_escape p else (let ch = src.[!i] in adv (); ch) in
      if !i >= n || src.[!i] <> '\'' then error p "字符字面量只能包含一个字节";
      adv ();
      push (INT (Char.code ch)) p
    end
    else if c = '"' then begin
      adv ();
      let parts = ref [] in
      let buf = Buffer.create 16 in
      let flush () =
        if Buffer.length buf > 0 then (parts := IPLit (Buffer.contents buf) :: !parts; Buffer.clear buf)
      in
      let fin = ref false in
      while not !fin do
        if !i >= n then error p "字符串未结束";
        let ch = src.[!i] in
        if ch = '"' then (adv (); fin := true)
        else if ch = '\\' then Buffer.add_char buf (read_escape p)
        else if ch = '#' && peek 1 = '{' then begin
          flush ();
          adv (); adv ();
          let cp = { line = !line; col = !col } in
          let b = !i and depth = ref 1 in
          while !depth > 0 do
            if !i >= n then error p "插值 #{ 未闭合";
            (match src.[!i] with '{' -> incr depth | '}' -> decr depth | _ -> ());
            if !depth > 0 then adv ()
          done;
          parts := IPCode (String.sub src b (!i - b), cp) :: !parts;
          adv ()
        end
        else (Buffer.add_char buf ch; adv ())
      done;
      flush ();
      match List.rev !parts with
      | [] -> push (STR "") p
      | [ IPLit s ] -> push (STR s) p
      | ps -> push (INTERP ps) p
    end
    else begin
      let two = if !i + 1 < n then String.sub src !i 2 else "" in
      let t2 = match two with
        | ".." -> Some DOTDOT | "->" -> Some ARROW | "=>" -> Some FATARROW
        | "==" -> Some EQEQ | "!=" -> Some NE | "<=" -> Some LE | ">=" -> Some GE
        | "&&" -> Some ANDAND | "||" -> Some OROR | "+=" -> Some PLUSEQ
        | "-=" -> Some MINUSEQ | "*=" -> Some STAREQ
        | _ -> None
      in
      match t2 with
      | Some t -> adv (); adv (); push t p
      | None ->
        let t = match c with
          | '(' -> stack := '(' :: !stack; LPAREN
          | '[' -> stack := '[' :: !stack; LBRACKET
          | '{' -> stack := '{' :: !stack; LBRACE
          | ')' | ']' | '}' ->
            (match !stack with _ :: r -> stack := r | [] -> error p "多余的 %c" c);
            (match c with ')' -> RPAREN | ']' -> RBRACKET | _ -> RBRACE)
          | ',' -> COMMA | ':' -> COLON | ';' -> SEMI | '.' -> DOT | '&' -> AMP
          | '+' -> PLUS | '-' -> MINUS | '*' -> STAR | '/' -> SLASH | '%' -> PERCENT
          | '<' -> LT | '>' -> GT | '!' -> BANG | '=' -> EQ
          | _ -> error p "无法识别的字符 '%c'" c
        in
        adv ();
        push t p
    end
  done;
  push NEWLINE { line = !line; col = !col };
  push EOF { line = !line; col = !col };
  Array.of_list (List.rev !toks)
