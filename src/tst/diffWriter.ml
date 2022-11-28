(**************************************************************************)
(* AU Compilation.                                                        *)
(**************************************************************************)

type diff = {test_name:string; phase_name: string; lines: string list}

let diffs_rev = ref ([]: diff list)

let logDiff test_name phase_name expected_name got_str =
  let (tmp_file, tmp_channel) = Filename.open_temp_file "dOvs_" "_diff" in
  output_string tmp_channel got_str; flush tmp_channel; close_out tmp_channel;
  let inp = Unix.open_process_in @@
    String.concat " " ["diff -u"; expected_name; tmp_file] in
  let lines = Stdio.In_channel.input_lines inp in
  Stdio.In_channel.close inp;
  let _: Unix.process_status = Unix.close_process_in inp in
  Sys.remove tmp_file;
  diffs_rev := {test_name; phase_name; lines}::(!diffs_rev)

let tag name ?(args=[]) content =
  let args_str =
    args |> List.map (fun (a,v) -> a ^ "=" ^ v)
         |> String.concat " " in
  String.concat "" ["<";name;" ";args_str;">";content;"</";name;">"]

let formatDiff lines =
  let is_prefix prefix str =
    try
    let size = String.length prefix in
    let test = String.sub str 0 size in
    String.equal prefix test
    with
    | _ -> false in
  let formatLine line =
    if is_prefix "+++" line then tag "span" ~args:["class","plus3"] line
    else if is_prefix "---" line then tag "span" ~args:["class","minus3"] line
    else if is_prefix "@@" line then tag "span" ~args:["class","at2"] line
    else if is_prefix "+" line  then tag "span" ~args:["class","plus"] line
    else if is_prefix "-" line then tag "span" ~args:["class","minus"] line
    else line in
  List.map formatLine lines

let writeResults out_file =
  let results = List.rev !diffs_rev in

  let summary = match List.length !diffs_rev with
  | 0 -> "All positive tests match expected files."
  | 1 -> "1 positive test differs from expected file."
  | n -> string_of_int n ^ " positive tests differ from expected files." in

  let formatResult {test_name;phase_name;lines} =
    let h2 = tag "button" ~args:[("type","button");("class","collapsible")]
             @@ phase_name ^ " : " ^ test_name in
    let diff = String.concat "\n" (formatDiff lines) in
    String.concat "\n" [h2; tag "div" ~args:["class","content"] @@ tag "pre" diff] in
  
  let diffs = List.map formatResult results in

  let title = "dOvs Diff" in
  let head =
    tag "head" @@ tag "title" title in
  let style = tag "style" @@ String.concat "\n"
    [ ".minus3   { color: blue;                       }"
    ; ".plus3    { color: maroon;                     }"
    ; ".at2      { color: lime;                       }"
    ; ".plus     { color: green; background: #E7E7E7; }"
    ; ".minus    { color: red;   background: #D7D7D7; }"

    ; ".collapsible {"
    ; " color: white;"
    ; " background-color: #A70000;"
    ; " cursor: pointer;"
    ; " padding: 15px;"
    ; " width: 100%;"
    ; " border: none;"
    ; " text-align: left;"
    ; " outline: none;"
    ; " font-size: 20px;"
    ; " margin-bottom: 5px;"
    ; " border-radius: 5px;"
    ; "}"

    ; ".active, .collapsible:hover {"
    ; " background-color: #E70000;"
    ; "}"

    ; "body {"
    ; " margin-left: 15%;"
    ; " margin-right: 15%;"
    ; "}"

    ; ".content {"
    ; " padding: 0 18px;"
    ; " display: none;"
    ; " overflow: hidden;"
    ; "}"] in

  let click_script = 
    String.concat "\n"
      [ "<script>"
      ; "var coll = document.getElementsByClassName(\"collapsible\");"
      ; "var i;"
      ; "for (i = 0; i < coll.length; i++) {"
      ; " coll[i].addEventListener(\"click\", function() {"
      ; "   this.classList.toggle(\"active\");"
      ; "   var content = this.nextElementSibling;"
      ; "   if (content.style.display === \"block\") {"
      ; "     content.style.display = \"none\";"
      ; "   } else {"
      ; "     content.style.display = \"block\";"
      ; "   }"
      ; " });"
      ; "}"
      ; "</script>"] in
  
  let h1 = tag "h1" @@ "dOvs diff" in

  let {Unix.tm_sec; tm_min; tm_hour; tm_mday; tm_mon; tm_year;_} =
      Unix.localtime @@ Unix.time() in

  let time = Printf.sprintf "%02d:%02d:%02d" tm_hour tm_min tm_sec in
  let date =
    Printf.sprintf "%02d-%02d-%04d" tm_mday (tm_mon + 1) (tm_year + 1900) in
  let time_str = String.concat " " ["Generated at";time;"on";date] in
  let body = tag "body" @@ tag "font" ~args:["size", "4"] @@
    String.concat "<br>\n" ([h1; time_str; summary; ""] @ diffs @ [click_script])
  in
  let html = tag "html" @@ String.concat "\n" [head; style; body] in
  Stdio.Out_channel.write_all out_file ~data:html
