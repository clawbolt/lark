(* Lark0 抽象语法树。类型检查会回填 ety / vid / is_decl 等可变字段。 *)

type pos = { line : int; col : int }

let dummy_pos = { line = 0; col = 0 }

exception Error of pos * string

let error pos fmt = Printf.ksprintf (fun s -> raise (Error (pos, s))) fmt

type ty =
  | TInt
  | TBool
  | TStr
  | TUnit
  | TNever               (* return / break / panic 等不返回的表达式 *)
  | TList of ty
  | TNamed of string     (* 解析时未区分 struct / enum *)
  | TStruct of string
  | TEnum of string
  | TUnknown             (* 尚未检查 *)

type mode = Read | Inout | Take

type binop = Add | Sub | Mul | Div | Mod | Eq | Ne | Lt | Le | Gt | Ge | And | Or

type unop = Neg | Not

type expr = {
  e : expr_kind;
  epos : pos;
  mutable ety : ty;
  mutable vid : int;           (* Var：解析后的局部变量编号 *)
  mutable resolved : resolved; (* Call：解析后的调用对象 *)
}

and expr_kind =
  | Int of int
  | Bool of bool
  | Str of string
  | Interp of expr list
  | Var of string
  | Field of expr * string
  | Index of expr * expr
  | Call of string * arg list
  | Method of expr * string * arg list
  | List of expr list
  | Unary of unop * expr
  | Binary of binop * expr * expr
  | If of expr * block * block option
  | Match of bool * expr * arm list   (* bool = take 模式 *)
  | Block of block
  | Return of expr option
  | Break
  | Continue

and arg = { label : string option; amp : bool; value : expr }

and arm = { pat : pattern; ppos : pos; body : expr }

and pattern =
  | PWild
  | PBind of string * binder
  | PInt of int
  | PBool of bool
  | PVariant of string * pattern_field list

and pattern_field = PFWild | PFBind of string * binder

and binder = { mutable bvid : int }

and block = { stmts : stmt list; tail : expr option }

and stmt = { s : stmt_kind; spos : pos }

and stmt_kind =
  | SAssign of expr * ty option * expr * decl_flag  (* 目标、可选类型标注、值 *)
  | SExpr of expr
  | SForCond of expr option * block
  | SForRange of string * binder * expr * expr * block
  | SForEach of string * binder * expr * block

and decl_flag = { mutable is_decl : bool }

and resolved =
  | RNone
  | RFn of string
  | RBuiltin of string
  | RStruct of string
  | RVariant of string * int    (* 枚举名、变体序号 *)

type param = { pname : string; pmode : mode; pty : ty; ppos_ : pos; mutable pvid : int }

type local_kind = LOwned | LRead | LInout

type local = {
  lname : string;
  cname : string;
  lty : ty;
  lkind : local_kind;
  loop_depth : int;
}

type fn_decl = {
  fname : string;
  params : param list;
  ret : ty;
  body : block;
  fpos : pos;
  mutable locals : (int, local) Hashtbl.t;
}

type field = { fdname : string; fdty : ty }

type variant = { vname : string; vfields : field list }

type item =
  | IStruct of string * field list * pos
  | IEnum of string * variant list * pos
  | IFn of fn_decl

let mk_expr pos e = { e; epos = pos; ety = TUnknown; vid = -1; resolved = RNone }

let rec show_ty = function
  | TInt -> "int"
  | TBool -> "bool"
  | TStr -> "str"
  | TUnit -> "()"
  | TNever -> "never"
  | TList t -> "[" ^ show_ty t ^ "]"
  | TNamed n | TStruct n | TEnum n -> n
  | TUnknown -> "?"

(* int / bool / () 为平凡类型；str 在 Lark0 中语义上可复制（不可变，运行时引用计数）。 *)
let is_trivial = function TInt | TBool | TUnit | TNever -> true | _ -> false

let is_copy t = is_trivial t || t = TStr
