module Html = Dom_html

let (>>=) = Lwt.bind

let replace_child p n =
  Js.Opt.iter (p##firstChild) (fun c -> Dom.removeChild p c);
  Dom.appendChild p n

let node x = (x : #Dom.node Js.t :> Dom.node Js.t)

let (<|) e l = List.iter (fun c -> Dom.appendChild e c) l; node e

let textnode s = Html.document##createTextNode (Js.string s)


let byID ty s = Js.Opt.get (ty (Html.getElementById s))
                           (fun () -> failwith ("Element " ^ s ^ " is of the wrong type"))

let node cls entries =
  let n = Html.createDiv Html.document in
  n##className <- Js.string cls;
  List.iter (fun c -> Dom.appendChild n c) entries;
  n

let update code =
  let modlist = Parser.modlist Lexer.read (Lexing.from_string code) in
  let types = Typecheck.infer_module modlist in

  let string_of_scheme (s : Typecheck.scheme) = 
    let (s : Types.var Types.typeterm) = Types.decompile_automaton s.Typecheck.expr in
    Types.(print_to_string (print_typeterm Pos) s) in

  let render_entry = Typecheck.(function
    | (n, Type s) -> node "binding" [node "name" [textnode n]; node "type" [textnode (string_of_scheme s)]]
    | (n, TypeError e) -> node "binding" [node "error" [textnode e]]) in

  let output = node "module" (List.map render_entry types) in
  replace_child (byID Html.CoerceTo.div "output") output

let focus_end textbox =
  (* it revolts me that this is how you put the
     cursor at the end of a textarea's text *)
  textbox##focus ();
  let v = textbox##value in
  textbox##value <- Js.string "";
  textbox##value <- v

let onload _ =
  let textbox = byID Html.CoerceTo.textarea "input" in
  let old_text = ref "????" in
  let oninput _ =
    let text = Js.to_string (textbox##value) in
    if text <> !old_text then update text;
    old_text := text;
    Js._false in
  let _ = oninput (Js.to_string (textbox##value)) in
  let _ = Html.addEventListener textbox Html.Event.input (Html.handler oninput) Js._false in
  focus_end textbox;
  Js._false

let _ =
  Html.window##onload <- Html.handler onload
