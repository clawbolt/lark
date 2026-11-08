(* lark0：Lark0 子集的引导编译器。用法：lark0 输入.lark [-o 输出.c] *)

let usage () =
  prerr_endline "用法：lark0 <输入.lark> [-o <输出.c>]";
  exit 2

let () =
  let input = ref None and output = ref None in
  let rec parse = function
    | "-o" :: o :: rest -> output := Some o; parse rest
    | ("-h" | "--help") :: _ -> usage ()
    | f :: rest when !input = None -> input := Some f; parse rest
    | [] -> ()
    | _ -> usage ()
  in
  parse (List.tl (Array.to_list Sys.argv));
  let input = match !input with Some f -> f | None -> usage () in
  let output =
    match !output with
    | Some o -> o
    | None -> Filename.remove_extension input ^ ".c"
  in
  let src =
    try In_channel.with_open_bin input In_channel.input_all
    with Sys_error m -> prerr_endline m; exit 1
  in
  try
    let items = Parser.parse_program src in
    let env, items = Check.check_program items in
    Own.check_program env items;
    let c = Codegen.gen_program env items in
    Out_channel.with_open_bin output (fun oc -> Out_channel.output_string oc c)
  with Ast.Error (p, msg) ->
    Printf.eprintf "%s:%d:%d: 错误：%s\n" input p.line p.col msg;
    exit 1
