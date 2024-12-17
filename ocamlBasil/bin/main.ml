open Yojson
open Lexing
open BasilIR
open BasilVisitor
open Lwt.Infix
open Lsp.Types
module IntMap = Map.Make (Int)
module IntSet = Set.Make (Int)

let oc = open_out "logger"

let log (s : string) =
  output_string oc (s ^ "\n");
  flush oc

(* offset -> linenum *)
type linebreaks = int IntMap.t

let get_begin_line (linebreaks : linebreaks) (char_pos : int) =
  match IntMap.find_last_opt (fun l -> l <= char_pos) linebreaks with
  | Some (charpos, x) -> charpos
  | None -> 0

let get_linenum (linebreaks : linebreaks) (char_pos : int) =
  match IntMap.find_last_opt (fun l -> l <= char_pos) linebreaks with
  | Some (charpos, linenum) -> linenum
  | None -> 0

module LineCol = struct
  type t = int * int

  let compare a b =
    match Int.compare (fst a) (fst b) with
    | 0 -> Int.compare (snd a) (snd b)
    | a -> a

  let pp l =
    "linecol(" ^ string_of_int (fst l) ^ "," ^ string_of_int (snd l) ^ ")"

  let create a b : t = (a, b)

  let to_position p =
    Linol_lwt.Position.create ~line:(fst p) ~character:(snd p)

  let range (b : t) (e : t) =
    Linol_lwt.Range.create ~start:(to_position b) ~end_:(to_position e)
end

module Token = struct
  (* order by start of token; we expect tokens to be disjoint *)
  (* (start, size) *)
  type t = LineCol.t * int

  let compare a b = LineCol.compare (fst a) (fst b)
  let create line column length = (LineCol.create line column, length)
  let begin_col (tok : t) : int = snd (fst tok)
  let end_col (tok : t) : int = begin_col tok + snd tok
  let line (tok : t) : int = fst (fst tok)
  let end_linecol t : LineCol.t = LineCol.create (line t) (end_col t)
  let begin_linecol t : LineCol.t = fst t
  let pp (t : t) : string = LineCol.pp (begin_linecol t)

  let to_range (t : t) =
    Linol_lwt.Range.create
      ~start:(LineCol.to_position (begin_linecol t))
      ~end_:(LineCol.to_position (end_linecol t))
end

module TokenMap = struct
  include Map.Make (Token)

  let pp = to_string
end

module StringMap = struct
  include Map.Make (String)

  let pp = to_string
end

type def_info = {
  label : string;
  label_tok : Token.t;
  range_start : LineCol.t;
  range_end : LineCol.t;
}

let range_of_position (linebreaks : linebreaks) (p1 : position)
    (p2 : position) : Lsp.Types.Range.t =
  let lsp_position (p : position) =
    let begin_line = get_begin_line linebreaks p.pos_cnum in
    Lsp.Types.Position.create ~character:(p.pos_cnum - begin_line)
      ~line:(p.pos_lnum - 1)
  in
  Lsp.Types.Range.create ~end_:(lsp_position p2) ~start:(lsp_position p1)

let token_of_char_range (linebreaks : linebreaks) (p1 : int) (p2 : int) :
    Token.t =
  let begin_line = get_begin_line linebreaks p1 in
  let line_no = get_linenum linebreaks p1 in
  let column = p1 - begin_line in
  let size = p2 - p1 in
  Token.create line_no column size

let token_of_bident (linebreaks : linebreaks) (id : AbsBasilIR.bIdent) :
    Token.t =
  match id with
  | AbsBasilIR.BIdent ((b, e), n) -> token_of_char_range linebreaks b e

let loc_of_char_pos (linebreaks : linebreaks) p : LineCol.t =
  LineCol.create (get_linenum linebreaks p) (p - get_begin_line linebreaks p)

let loc_of_beginrec (linebreaks : linebreaks) id : LineCol.t =
  match id with
  | AbsBasilIR.BeginRec ((b, e), n) -> loc_of_char_pos linebreaks b

let loc_of_endrec (linebreaks : linebreaks) id : LineCol.t =
  match id with
  | AbsBasilIR.EndRec ((b, e), n) -> loc_of_char_pos linebreaks e

let loc_of_beginlist (linebreaks : linebreaks) id : LineCol.t =
  match id with
  | AbsBasilIR.BeginList ((b, e), n) -> loc_of_char_pos linebreaks b

let loc_of_endlist (linebreaks : linebreaks) id : LineCol.t =
  match id with
  | AbsBasilIR.EndList ((b, e), n) -> loc_of_char_pos linebreaks e

let find_token_opt (tokens : 'a TokenMap.t) (pos : LineCol.t) : 'a option =
  TokenMap.find_last_opt (fun t -> LineCol.compare (fst t) pos <= 0) tokens
  |> function
  | Some (t, r)
    when let pos_col = snd pos in
         Token.line t == fst pos
         && Token.begin_col t <= pos_col
         && Token.end_col t >= pos_col ->
      Some r
  | _ -> None

module Processor = struct
  open BasilIR.AbsBasilIR

  type symbs = {
    proc_defs : def_info StringMap.t;
    proc_children : string list StringMap.t;
    block_defs : def_info StringMap.t;
    proc_refs : string TokenMap.t;
    block_refs : string TokenMap.t;
  }

  let get_syms (s : symbs) : DocumentSymbol.t list =
    let block_sym (blockname : string) (def : def_info) =
      Linol_lwt.DocumentSymbol.create ~kind:Lsp.Types.SymbolKind.Method
        ~name:blockname
        ~selectionRange:(Token.to_range def.label_tok)
        ~range:(LineCol.range def.range_start def.range_end)
        ()
    in
    let proc_sym (procname : string) (def : def_info) =
      let children =
        StringMap.find procname s.proc_children
        |> List.map (fun n -> (n, StringMap.find n s.block_defs))
        |> List.map (fun (id, t) -> block_sym id t)
      in
      Linol_lwt.DocumentSymbol.create ~children
        ~kind:Lsp.Types.SymbolKind.Class ~name:procname
        ~selectionRange:(Token.to_range def.label_tok)
        ~range:(LineCol.range def.range_start def.range_end)
        ()
    in
    StringMap.to_list s.proc_defs |> List.map (fun (s, t) -> proc_sym s t)

  let print_syms (s : symbs) =
    log "procdefs\n";
    StringMap.iter
      (fun a b -> log (a ^ " @ " ^ Token.pp b.label_tok ^ "\n"))
      s.proc_defs;
    log "block defs\n";
    StringMap.iter
      (fun a b -> log (a ^ " @ " ^ Token.pp b.label_tok ^ "\n"))
      s.block_defs;
    log "proc refs\n";
    TokenMap.iter
      (fun a b -> log (b ^ " @ " ^ Token.pp a ^ "\n"))
      s.proc_refs;
    log "block refs\n";
    TokenMap.iter
      (fun a b -> log (b ^ " @ " ^ Token.pp a ^ "\n"))
      s.block_refs

  let find_definition (s : symbs) (line_num : int) (col_num : int) :
      def_info option =
    let r = LineCol.create line_num col_num in
    let find m i =
      Option.bind i (fun (x : string) -> StringMap.find_opt x m)
    in
    match find_token_opt s.block_refs r |> find s.block_defs with
    | None -> find_token_opt s.proc_refs r |> find s.proc_defs
    | x -> x

  let unpack_ident id linebreaks =
    match id with BIdent (_, n) -> (token_of_bident linebreaks id, n)

  let linebreaks (s : string) : linebreaks =
    let count = ref 0 in
    let breaks =
      Seq.filter_map
        (* next char is beginning of a line *)
          (fun (i, c) ->
          match c with
          | '\n' ->
              count := !count + 1;
              Some (i + 1, !count)
          | _ -> None)
        (String.to_seqi s)
    in
    IntMap.add 0 0 @@ IntMap.add_seq breaks IntMap.empty

  class getBlocks (linebreaks : linebreaks) =
    object
      (* procid, blockid *)
      val mutable current_proc : string option = None
      val mutable proc_defs : def_info StringMap.t = StringMap.empty
      val mutable proc_children : string list StringMap.t = StringMap.empty

      (* containing procedure key, block identifier key *)
      val mutable block_defs : def_info StringMap.t = StringMap.empty
      val mutable proc_refs : string TokenMap.t = TokenMap.empty
      val mutable block_refs : string TokenMap.t = TokenMap.empty
      inherit nopBasilVisitor
      method get_block_defs = block_defs
      method get_block_refs = block_refs
      method get_proc_defs = proc_defs
      method get_proc_refs = proc_refs
      method get_proc_children = proc_children

      method! vjump (j : jump) =
        (match j with
        | GoTo idents ->
            List.iter
              (fun id ->
                let pos, id = unpack_ident id linebreaks in
                block_refs <- TokenMap.add pos id block_refs)
              idents
        | _ -> ());
        SkipChildren

      method! vstmt (s : statement) =
        let r =
          match s with DirectCall (_, id, _) -> Some id | _ -> None
        in
        Option.iter
          (fun id ->
            let pos, ident = unpack_ident id linebreaks in
            proc_refs <- TokenMap.add pos ident proc_refs)
          r;
        SkipChildren

      method! vproc (p : bIdent * procDef) =
        let b, e =
          match p with
          | ( bi,
              PD
                ( beginRec,
                  str,
                  pAddress,
                  pEntry,
                  pExit,
                  internalBlocks,
                  endRec ) ) ->
              (beginRec, endRec)
        in
        let pos, id = unpack_ident (fst p) linebreaks in
        let pd : def_info =
          {
            label = id;
            label_tok = pos;
            range_start = Token.begin_linecol pos;
            range_end = loc_of_endrec linebreaks e;
          }
        in
        proc_defs <- StringMap.add id pd proc_defs;
        current_proc <- Some id;
        proc_children <- StringMap.add id [] proc_children;
        DoChildren

      method! vblock (b : block) =
        match b with
        | B (id, _, bg, _, _, ed) ->
            let pos, id = unpack_ident id linebreaks in
            let proc = Option.get current_proc in
            let nblocks = id :: StringMap.find proc proc_children in
            let blockdef =
              {
                label = id;
                label_tok = pos;
                range_start = Token.begin_linecol pos;
                range_end = loc_of_endlist linebreaks ed;
              }
            in
            proc_children <- StringMap.add proc nblocks proc_children;
            block_defs <- StringMap.add id blockdef block_defs;
            DoChildren
    end

  let get_symbs (linebreaks : linebreaks) (p : program) =
    let vis = new getBlocks linebreaks in
    let _ = visit_prog vis p in
    {
      proc_defs = vis#get_proc_defs;
      proc_children = vis#get_proc_children;
      block_defs = vis#get_block_defs;
      proc_refs = vis#get_proc_refs;
      block_refs = vis#get_block_refs;
    }
end

let parse (c : in_channel) : AbsBasilIR.program =
  let lexbuf = Lexing.from_channel c in
  try ParBasilIR.pProgram LexBasilIR.token lexbuf
  with ParBasilIR.Error ->
    let start_pos = Lexing.lexeme_start_p lexbuf
    and end_pos = Lexing.lexeme_end_p lexbuf in
    raise (BNFC_Util.Parse_error (start_pos, end_pos))

let showTree (t : AbsBasilIR.program) : string =
  "[Linearized tree]\n\n"
  ^ PrintBasilIR.printTree PrintBasilIR.prtProgram t
  ^ "\n"

type doc_ast =
  | SyntaxError of (string * position * position)
  | Ast of AbsBasilIR.program * Processor.symbs

type state_after_processing = {
  linebreaks : linebreaks;
  ast : doc_ast;
  procs : BasilAST.BasilAST.proc list;
}

let process (s : string) : state_after_processing =
  let lexbuf = Lexing.from_string s in
  let linebreaks = Processor.linebreaks s in
  try
    let prog = ParBasilIR.pProgram LexBasilIR.token lexbuf in
    let syms = Processor.get_symbs linebreaks prog in
    let procs = try (
      let procs = BasilAST.BasilASTLoader.transProgram prog in
      let oc = open_out "show" in
      List.map (fun p -> BasilAST.BasilAST.show_proc p) procs 
        |> List.iter (fun s -> output_string oc s);
      procs
    )
      with 
        | exn -> (
          let e = Printexc.to_string exn in
          log (Printf.sprintf "%s:\n" e) ;
          Printexc.print_backtrace oc ;
          []
      )
  in
    (*Processor.print_syms syms; *)
    { linebreaks; ast = Ast (prog, syms); procs }
  with ParBasilIR.Error ->
    let start_pos = Lexing.lexeme_start_p lexbuf
    and end_pos = Lexing.lexeme_end_p lexbuf in
    {
      linebreaks;
      ast = SyntaxError (lexeme lexbuf, start_pos, end_pos);
      procs = [];
    }

let process_some_input_file (_file_contents : string) :
    state_after_processing =
  process _file_contents

let diagnostics (_state : state_after_processing) :
    Lsp.Types.Diagnostic.t list =
  match _state.ast with
  | Ast _ -> []
  | SyntaxError (l, p1, p2) ->
      [
        Lsp.Types.Diagnostic.create
          ~message:("Syntax error: '" ^ l ^ "'")
          ~range:(range_of_position _state.linebreaks p1 p2)
          ~severity:Lsp.Types.DiagnosticSeverity.Error ();
      ]

open Linol_lwt.Locations
open Linol_lwt

class lsp_server =
  object (self)
    inherit Linol_lwt.Jsonrpc2.server

    (* one env per document *)
    val buffers : (Lsp.Types.DocumentUri.t, state_after_processing) Hashtbl.t
        =
      Hashtbl.create 32

    method spawn_query_handler f = Linol_lwt.spawn f
    method! config_definition = Some (`Bool true)

    method! config_symbol =
      Some
        (`DocumentSymbolOptions
          (DocumentSymbolOptions.create ~label:"symbols"
             ~workDoneProgress:true ()))

    method private _on_doc ~(notify_back : Linol_lwt.Jsonrpc2.notify_back)
        (uri : Lsp.Types.DocumentUri.t) (contents : string) =
      let new_state = process_some_input_file contents in
      Hashtbl.replace buffers uri new_state;
      let diags = diagnostics new_state in
      notify_back#send_diagnostic diags

    (* We now override the [on_notify_doc_did_open] method that will be
       called by the server each time a new document is opened. *)
    method on_notif_doc_did_open ~notify_back d ~content : unit Linol_lwt.t =
      self#_on_doc ~notify_back d.uri content

    (* Similarly, we also override the [on_notify_doc_did_change] method that
       will be called by the server each time a new document is opened. *)
    method on_notif_doc_did_change ~notify_back d _c ~old_content:_old
        ~new_content =
      self#_on_doc ~notify_back d.uri new_content

    method on_req_hover ~notify_back ~id ~uri ~pos ~workDoneToken
        (d : Linol_lwt.doc_state) =
      Lwt.return None

    (* `Location of Location.t list *)
    method on_req_definition ~notify_back ~id ~uri ~pos ~workDoneToken
        ~partialResultToken d : Linol_lwt.Locations.t option Lwt.t =
      log "req_definition ";
      (match (Hashtbl.find buffers d.uri).ast with
      | Ast (p, syms) ->
          log
            ("get definition : " ^ string_of_int pos.line ^ " "
            ^ string_of_int pos.character);
          Processor.find_definition syms pos.line pos.character
      | _ -> None)
      |> Option.map (fun def ->
             `Location
               [
                 Linol_lwt.Location.create
                   ~range:(Token.to_range def.label_tok)
                   ~uri;
               ])
      |> Lwt.return

    method on_req_symbol ~notify_back ~id ~uri ~workDoneToken
        ~partialResultToken e =
      log "req syms";
      (*(notify_back#work_done_progress_begin (WorkDoneProgressBegin.create
        ~title:"symbols" ())) >>= fun e ->
        (notify_back#work_done_progress_end (WorkDoneProgressEnd.create
        ~message:"completed" ())) >>= *)
      let r =
        (match (Hashtbl.find buffers uri).ast with
        | Ast (p, syms) -> Some syms
        | _ -> None)
        |> Option.map (fun s -> Processor.get_syms s)
        |> Option.map (fun x -> `DocumentSymbol x)
      in
      (function Some x -> log "syms" | None -> log "no syms") r;
      Lwt.return r

    (* On document closes, we remove the state associated to the file from
       the global hashtable state, to avoid leaking memory. *)
    method on_notif_doc_did_close ~notify_back:_ d : unit Linol_lwt.t =
      Hashtbl.remove buffers d.uri;
      Linol_lwt.return ()
  end

(* Main code This is the code that creates an instance of the lsp server
   class and runs it as a task. *)
let run () =
  log "start";
  let s = new lsp_server in
  let server = Linol_lwt.Jsonrpc2.create_stdio ~env:() s in
  let task =
    let shutdown () = s#get_status = `ReceivedExit in
    Linol_lwt.Jsonrpc2.run ~shutdown server
  in
  match Linol_lwt.run task with
  | () -> ()
  | exception e ->
      let e = Printexc.to_string e in
      Printf.fprintf oc "error: %s\n%!" e;
      exit 1

let () =
  Printexc.record_backtrace true;
  run ()
(* Finally, we actually run the server *)
