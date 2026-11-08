(* C 代码生成：类型布局、析构/复制/列表辅助函数。 *)
open Ast

let rec mangle = function
  | TInt -> "i"
  | TBool -> "b"
  | TStr -> "s"
  | TUnit | TNever -> "v"
  | TStruct n -> "S" ^ string_of_int (String.length n) ^ n
  | TEnum n -> "E" ^ string_of_int (String.length n) ^ n
  | TList t -> "L" ^ mangle t
  | TNamed n -> failwith ("内部错误：未解析的类型 " ^ n)
  | TUnknown -> failwith "内部错误：未知类型"

(* 用到的列表类型，按依赖顺序登记（元素类型先登记） *)
let lists : (string, unit) Hashtbl.t = Hashtbl.create 16
let list_order : ty list ref = ref []

let rec register t =
  match t with
  | TList e ->
    let m = mangle t in
    if not (Hashtbl.mem lists m) then begin
      register e;
      Hashtbl.replace lists m ();
      list_order := !list_order @ [ t ]
    end
  | _ -> ()

let ctype t =
  register t;
  match t with
  | TInt -> "int64_t"
  | TBool -> "bool"
  | TStr -> "lk_str"
  | TUnit | TNever -> "void"
  | TStruct n -> "S_" ^ n
  | TEnum n -> "E_" ^ n
  | TList _ -> "LK_" ^ mangle t
  | TNamed _ | TUnknown -> failwith "内部错误：ctype"

let managed t = not (is_trivial t)

let drop_stmt t place =
  if managed t then Printf.sprintf "lk_drop_%s(&(%s));" (mangle t) place else ""

let copy_expr t place =
  if managed t then Printf.sprintf "lk_copy_%s(&(%s))" (mangle t) place else place

let fname f = "f_" ^ f
let fld f = "f_" ^ f

(* 结构体按值包含关系做拓扑排序 *)
let sort_structs env (names : string list) : string list =
  let state = Hashtbl.create 16 and out = ref [] in
  let rec visit n =
    match Hashtbl.find_opt state n with
    | Some `Done -> ()
    | Some `Active -> error dummy_pos "结构体 %s 按值包含了自己，请改用 enum 或列表" n
    | None ->
      Hashtbl.replace state n `Active;
      List.iter
        (fun f -> match f.fdty with TStruct m -> visit m | _ -> ())
        (Hashtbl.find env.Check.structs n);
      Hashtbl.replace state n `Done;
      out := n :: !out
  in
  List.iter visit names;
  List.rev !out

let emit_types (env : Check.env) (items : item list) : string =
  let b = Buffer.create 4096 in
  let p fmt = Printf.bprintf b fmt in
  let structs = List.filter_map (function IStruct (n, _, _) -> Some n | _ -> None) items in
  let enums = List.filter_map (function IEnum (n, vs, _) -> Some (n, vs) | _ -> None) items in
  List.iter (fun n -> List.iter (fun f -> register f.fdty) (Hashtbl.find env.Check.structs n)) structs;
  List.iter (fun (_, vs) -> List.iter (fun v -> List.iter (fun f -> register f.fdty) v.vfields) vs) enums;
  let structs = sort_structs env structs in
  let lists = !list_order in
  (* 前向声明 *)
  List.iter (fun n -> p "typedef struct S_%s S_%s;\n" n n) structs;
  List.iter (fun (n, _) -> p "typedef struct E_%s_s* E_%s;\n" n n) enums;
  List.iter (fun t -> let c = ctype t in p "typedef struct %s %s;\n" c c) lists;
  p "\n";
  List.iter
    (fun t ->
       match t with
       | TList e -> p "struct %s { %s* data; int64_t len; int64_t cap; };\n" (ctype t) (ctype e)
       | _ -> ())
    lists;
  List.iter
    (fun n ->
       p "struct S_%s {" n;
       let fs = Hashtbl.find env.Check.structs n in
       if fs = [] then p " char _empty;";
       List.iter (fun f -> p " %s %s;" (ctype f.fdty) (fld f.fdname)) fs;
       p " };\n")
    structs;
  List.iter
    (fun (n, vs) ->
       p "struct E_%s_s { int32_t tag; union { char _empty;" n;
       List.iteri
         (fun i v ->
            if v.vfields <> [] then begin
              p " struct {";
              List.iter (fun f -> p " %s %s;" (ctype f.fdty) (fld f.fdname)) v.vfields;
              p " } v%d;" i
            end)
         vs;
       p " } u; };\n")
    enums;
  p "\n";
  (* 原型 *)
  let all_types =
    List.map (fun n -> TStruct n) structs @ List.map (fun (n, _) -> TEnum n) enums @ lists
  in
  List.iter
    (fun t ->
       let c = ctype t and m = mangle t in
       p "static void lk_drop_%s(%s* p);\nstatic %s lk_copy_%s(%s* p);\n" m c c m c)
    all_types;
  List.iter
    (fun (n, vs) ->
       List.iteri
         (fun i v ->
            let ps = List.mapi (fun j f -> Printf.sprintf "%s a%d" (ctype f.fdty) j) v.vfields in
            p "static E_%s lk_mk_%s_%d(%s);\n" n (mangle (TEnum n)) i
              (if ps = [] then "void" else String.concat ", " ps))
         vs)
    enums;
  p "\n";
  (* 结构体辅助函数 *)
  List.iter
    (fun n ->
       let t = TStruct n in
       let c = ctype t and m = mangle t in
       let fs = Hashtbl.find env.Check.structs n in
       p "static void lk_drop_%s(%s* p) {" m c;
       List.iter (fun f -> p " %s" (drop_stmt f.fdty ("p->" ^ fld f.fdname))) fs;
       p " (void)p; }\n";
       p "static %s lk_copy_%s(%s* p) { %s r = {0};" c m c c;
       List.iter (fun f -> p " r.%s = %s;" (fld f.fdname) (copy_expr f.fdty ("p->" ^ fld f.fdname))) fs;
       p " (void)p; return r; }\n")
    structs;
  (* 枚举辅助函数 *)
  List.iter
    (fun (n, vs) ->
       let t = TEnum n in
       let c = ctype t and m = mangle t in
       p "static void lk_drop_%s(%s* p) { %s e = *p; if (!e) return; *p = NULL; switch (e->tag) {" m c c;
       List.iteri
         (fun i v ->
            p " case %d:" i;
            List.iter (fun f -> p " %s" (drop_stmt f.fdty (Printf.sprintf "e->u.v%d.%s" i (fld f.fdname)))) v.vfields;
            p " break;")
         vs;
       p " default: break; } free(e); }\n";
       p "static %s lk_copy_%s(%s* p) { %s e = *p; if (!e) return NULL; %s r = lk_alloc(sizeof *r); r->tag = e->tag; switch (e->tag) {" c m c c c;
       List.iteri
         (fun i v ->
            p " case %d:" i;
            List.iter
              (fun f ->
                 let fl = Printf.sprintf "u.v%d.%s" i (fld f.fdname) in
                 p " r->%s = %s;" fl (copy_expr f.fdty ("e->" ^ fl)))
              v.vfields;
            p " break;")
         vs;
       p " default: break; } return r; }\n";
       List.iteri
         (fun i v ->
            let ps = List.mapi (fun j f -> Printf.sprintf "%s a%d" (ctype f.fdty) j) v.vfields in
            p "static %s lk_mk_%s_%d(%s) { %s r = lk_alloc(sizeof *r); r->tag = %d;" c m i
              (if ps = [] then "void" else String.concat ", " ps) c i;
            List.iteri (fun j f -> p " r->u.v%d.%s = a%d;" i (fld f.fdname) j) v.vfields;
            p " return r; }\n")
         vs)
    enums;
  (* 列表辅助函数 *)
  List.iter
    (fun t ->
       match t with
       | TList e ->
         let c = ctype t and m = mangle t and ce = ctype e in
         p "static void lk_drop_%s(%s* p) {" m c;
         if managed e then p " for (int64_t i = 0; i < p->len; i++) %s" (drop_stmt e "p->data[i]");
         p " free(p->data); p->data = NULL; p->len = p->cap = 0; }\n";
         p "static %s lk_copy_%s(%s* p) { %s r; r.len = p->len; r.cap = p->len; r.data = p->len ? lk_alloc(sizeof(%s) * p->len) : NULL;" c m c c ce;
         p " for (int64_t i = 0; i < p->len; i++) r.data[i] = %s; return r; }\n" (copy_expr e "p->data[i]");
         p "static void lk_push_%s(%s* p, %s v) { if (p->len == p->cap) { p->cap = p->cap ? p->cap * 2 : 4; p->data = lk_realloc(p->data, sizeof(%s) * p->cap); } p->data[p->len++] = v; }\n" m c ce ce;
         p "static %s lk_pop_%s(%s* p) { if (p->len == 0) lk_panic_c(\"pop: 列表为空\"); return p->data[--p->len]; }\n" ce m c;
         p "static %s* lk_at_%s(%s* p, int64_t i) { if (i < 0 || i >= p->len) lk_index_oob(i, p->len); return &p->data[i]; }\n" ce m c
       | _ -> ())
    lists;
  Buffer.contents b
