open Yojson
open Lexing
open Loader
open BasilVisitor
open Lwt.Infix
open Lsp.Types
open BasilIR
module IntMap = Map.Make (Int)
module IntSet = Set.Make (Int)

let debug = true
let oc = if debug then Some (open_out ".basillsplog") else None

let bident_of_blockident = function
  | AbsBasilIR.BlockIdent x -> AbsBasilIR.BIdent x

let bident_of_procident = function
  | AbsBasilIR.ProcIdent x -> AbsBasilIR.BIdent x

let log (s : string) =
  Option.iter
    (fun oc ->
      output_string oc (s ^ "\n");
      flush oc)
    oc

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

  let show x =
    let l, c = x in
    Printf.sprintf "(line: %d), (col: %d)" l c

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

  let show (x : t) =
    let l, c = x in
    Printf.sprintf "(line: %s), (size: %d)" (LineCol.show l) c

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
    (p2 : position) : Linol_lsp.Types.Range.t =
  let lsp_position (p : position) =
    let begin_line = get_begin_line linebreaks p.pos_cnum in
    Linol_lsp.Types.Position.create ~character:(p.pos_cnum - begin_line)
      ~line:(p.pos_lnum - 1)
  in
  Linol_lsp.Types.Range.create ~end_:(lsp_position p2)
    ~start:(lsp_position p1)

let token_of_char_range (linebreaks : linebreaks) (p1 : int) (p2 : int) :
    Token.t =
  let begin_line = get_begin_line linebreaks p1 in
  let line_no = get_linenum linebreaks p1 in
  let column = p1 - begin_line in
  let size = p2 - p1 in
  Token.create line_no column size

let token_of_lexer_token (linebreaks : linebreaks)
    (token : (int * int) * string) : Token.t =
  let (b, e), n = token in
  token_of_char_range linebreaks b e

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

module SemanticTokensProcessor = struct
  type token_info = { token_type : string; token_modifiers : string list }
  [@@deriving show]

  type t = token_info TokenMap.t

  let lex_tokens_of_string linebreaks s =
    let open Kwtypes in
    let lexbuf = Lexing.from_string s in
    let tp = Parkeywords.kwl Lexkeywords.token lexbuf in
    List.iter (fun i -> log (Kwtypes.show_parsed i)) tp;
    tp
    |> List.filter_map (function
         | Keyword ((b, e), i) ->
             Some
               ( token_of_char_range linebreaks b e,
                 { token_type = "keyword"; token_modifiers = [] } )
         | _ -> None)
    |> TokenMap.of_list

  let show (x : t) =
    x |> TokenMap.to_list
    |> List.map (fun (k, v) ->
           Printf.sprintf "%s : %s" (Token.show k) (show_token_info v))
    |> String.concat "\n"

  (* dealing with int-indexed tokens *)
  let token_mod = [ "declaration"; "definition" ]

  let token_typ =
    [
      "class";
      "method";
      "function";
      "variable";
      "type";
      "number";
      "parameter";
      "keyword";
    ]

  let to_index m = List.mapi (fun i v -> (v, i)) m |> StringMap.of_list

  let get_token_mod : string -> int =
    let m = to_index token_mod in
    fun i -> StringMap.find i m

  let get_token_typ : string -> int =
    let m = to_index token_typ in
    fun i -> StringMap.find i m

  (*TODO: probably want to implement ranges for efficiency*)
  let semantic_tokens_config =
    let stoken_legend =
      Linol_lwt.SemanticTokensLegend.create ~tokenModifiers:token_mod
        ~tokenTypes:token_typ
    in
    Linol_lwt.SemanticTokensRegistrationOptions.create
      ~full:
        (`Full
           (Linol_lwt.SemanticTokensRegistrationOptions.create_full
              ~delta:false ()))
      ~legend:stoken_legend ()

  let token_to_array (tok : Token.t) (tok_info : token_info) =
    (* https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#textDocument_semanticTokens *)
    let { token_type; token_modifiers } = tok_info in
    let line, character = fst tok in
    let length = snd tok in
    let token_modifiers = List.map get_token_mod token_mod in
    let token_type = get_token_typ token_type in
    let modifier_bitset =
      List.map (fun i -> Int.shift_left 1 i) token_modifiers
      |> List.fold_left Int.logor 0
    in
    [| line; character; length; token_type; modifier_bitset |]

  let empty = TokenMap.empty

  let add_one (key : Token.t) ~(token_type : string) ?(token_modifiers = [])
      m =
    TokenMap.add key { token_type; token_modifiers } m

  let add xs (e : 'a -> Token.t * token_info) tm =
    Seq.map e xs |> fun x -> TokenMap.add_seq x tm

  let add_tokmap (xs : 'a TokenMap.t) (e : token_info) tm =
    let ns = TokenMap.map (fun _ -> e) xs in
    TokenMap.union (fun i a b -> Some a) tm ns

  let linecol_relative_to (i : LineCol.t) (j : LineCol.t) =
    let l_i, p_i = i in
    let l_j, p_j = j in
    if l_i = l_j then (0, p_j - p_i) else (l_j - l_i, p_j)

  let token_relative_to (i : Token.t) (j : Token.t) =
    (linecol_relative_to (fst i) (fst j), snd j)

  let to_semantic_tokens_full (tokens : t) =
    (*NOTE: assuming non-overlapping without checking: grammar shouldn't
      allow *)
    let sorted = TokenMap.to_list tokens in
    let relative =
      match sorted with
      | [] -> []
      | hd :: [] -> [ hd ]
      | hd :: tl ->
          let _, nl =
            List.fold_left_map
              (fun ptok (tok, ti) ->
                let nt = token_relative_to ptok tok in
                (tok, (nt, ti)))
              (fst hd) tl
          in
          hd :: nl
    in
    let data =
      List.map (fun (t, i) -> token_to_array t i) relative |> Array.concat
    in
    Linol_lwt.SemanticTokens.create ~data ()
end

module Processor = struct
  open BasilIR.AbsBasilIR

  type symbs = {
    proc_defs : def_info StringMap.t;
    proc_children : string list StringMap.t;
    block_defs : def_info StringMap.t;
    proc_refs : string TokenMap.t;
    block_refs : string TokenMap.t;
    all_tokens : SemanticTokensProcessor.t;
  }

  let to_semantic_highlight_data (s : symbs) =
    log (SemanticTokensProcessor.show s.all_tokens);
    let toks =
      SemanticTokensProcessor.empty
      |> SemanticTokensProcessor.add (StringMap.to_seq s.proc_defs)
           (fun (_, di) ->
             ( di.label_tok,
               { token_type = "class"; token_modifiers = [ "definition" ] }
             ))
      |> SemanticTokensProcessor.add (StringMap.to_rev_seq s.block_defs)
           (fun (_, di) ->
             ( di.label_tok,
               { token_type = "method"; token_modifiers = [ "definition" ] }
             ))
      |> SemanticTokensProcessor.add_tokmap s.block_refs
           { token_type = "method"; token_modifiers = [] }
      |> SemanticTokensProcessor.add_tokmap s.proc_refs
           { token_type = "class"; token_modifiers = [] }
      |> TokenMap.union (fun i a b -> Some a) s.all_tokens
    in
    SemanticTokensProcessor.to_semantic_tokens_full toks

  let get_syms (s : symbs) : Linol_lwt.DocumentSymbol.t list =
    let block_sym (blockname : string) (def : def_info) =
      Linol_lwt.DocumentSymbol.create ~kind:Linol_lsp.Types.SymbolKind.Method
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
        ~kind:Linol_lsp.Types.SymbolKind.Class ~name:procname
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

  let unpack_blockident id linebreaks =
    match id with
    | BlockIdent (_, n) ->
        (token_of_bident linebreaks (bident_of_blockident id), n)

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

  let rec type_idents (t : typeT) =
    match t with
    | TypeBVType (BVT (BVTYPE t)) -> [ t ]
    | TypeIntType (IntT (INTTYPE t)) -> [ t ]
    | TypeBoolType (BoolT (BOOLTYPE t)) -> [ t ]
    | TypeMapType (MapT (t1, t2)) -> type_idents t1 @ type_idents t2

  let pos_of_intval t =
    match t with HexInt (IntegerHex i) -> i | DecInt (IntegerDec i) -> i

  class getTokens (linebreaks : linebreaks) =
    object (self)
      val mutable tokens : SemanticTokensProcessor.t =
        SemanticTokensProcessor.empty

      inherit nopBasilVisitor
      method get_tokens () = tokens

      method add_tok (t : (int * int) * string) (token_type : string) : unit
          =
        let tok = token_of_lexer_token linebreaks t in
        tokens <- SemanticTokensProcessor.add_one tok ~token_type tokens

      method add_tok_modifiers (t : (int * int) * string)
          (token_type : string) (token_modifiers : string list) : unit =
        let tok = token_of_lexer_token linebreaks t in
        tokens <-
          SemanticTokensProcessor.add_one tok ~token_type ~token_modifiers
            tokens

      method! vlvar (lv : lVar) =
        match lv with
        | LVarDef (LocalVar1 (LocalIdent i, t)) ->
            self#add_tok i "variable";
            type_idents t |> List.iter (fun i -> self#add_tok i "type");
            SkipChildren
        | GlobalLVar (GlobalVar1 (GlobalIdent i, t)) ->
            self#add_tok i "variable";
            type_idents t |> List.iter (fun i -> self#add_tok i "type");
            SkipChildren

      method! vdecl (p : declaration) =
        log "vdecl";
        (match p with
        | AxiomDecl _ -> ()
        | ProgDecl (ProcIdent i, _) -> self#add_tok_modifiers i "class" []
        | ProgDeclWithSpec (ProcIdent i, _, _, _, _) ->
            self#add_tok_modifiers i "class" []
        | SharedMemDecl (GlobalIdent i, t) ->
            type_idents t |> List.iter (fun i -> self#add_tok i "type");
            self#add_tok_modifiers i "variable" [ "declaration" ]
        | UnsharedMemDecl (GlobalIdent i, t) ->
            type_idents t |> List.iter (fun i -> self#add_tok i "type");
            self#add_tok_modifiers i "variable" [ "declaration" ]
        | VarDecl (GlobalIdent i, t) ->
            type_idents t |> List.iter (fun i -> self#add_tok i "type");
            self#add_tok_modifiers i "variable" [ "declaration" ]
        | UninterpFunDecl (attr, GlobalIdent i, ts, t) ->
            List.concat_map type_idents (t :: ts)
            |> List.iter (fun i -> self#add_tok i "type");
            self#add_tok_modifiers i "function" [ "declaration" ]
        | FunDef (attr, GlobalIdent i, _, t, _) ->
            type_idents t |> List.iter (fun i -> self#add_tok i "type");
            self#add_tok_modifiers i "function" [ "declaration" ]
        | Procedure
            (ProcedureSig (ProcIdent i, inparams, outparams), attrs, def) ->
            let of_param = function
              | Param (LocalIdent i, t) ->
                  self#add_tok i "parameter";
                  type_idents t |> List.iter (fun i -> self#add_tok i "type")
            in
            List.iter of_param inparams;
            List.iter of_param outparams;
            self#add_tok_modifiers i "class" [ "declaration" ]);
        DoChildren

      method! vstmt (s : statement) =
        match s with
        | SLoad (lv, _, GlobalIdent i, exp, iv) ->
            self#add_tok (pos_of_intval iv) "number";
            self#add_tok i "variable";
            DoChildren
        | SStore (_, GlobalIdent i, _, _, iv) ->
            self#add_tok i "variable";
            self#add_tok (pos_of_intval iv) "number";
            DoChildren
        | _ -> DoChildren

      method! vexpr (e : expr) =
        log "vexp";
        match e with
        | FunctionOp (GlobalIdent i, p) ->
            self#add_tok i "function";
            DoChildren
        | GRVar (GlobalVar1 (GlobalIdent i, t)) ->
            self#add_tok i "variable";
            List.iter (fun i -> self#add_tok i "type") (type_idents t);
            SkipChildren
        | LRVar (LocalVar1 (LocalIdent i, t)) ->
            self#add_tok i "variable";
            List.iter (fun i -> self#add_tok i "type") (type_idents t);
            SkipChildren
        | Literal (IntLiteral (HexInt (IntegerHex i))) ->
            self#add_tok i "number";
            SkipChildren
        | Literal (IntLiteral (DecInt (IntegerDec i))) ->
            self#add_tok i "number";
            SkipChildren
        | Literal (BVLiteral (BV (HexInt (IntegerHex i), BVT (BVTYPE t)))) ->
            self#add_tok i "number";
            self#add_tok t "type";
            SkipChildren
        | Literal (BVLiteral (BV (DecInt (IntegerDec i), BVT (BVTYPE t)))) ->
            self#add_tok i "number";
            self#add_tok t "type";
            SkipChildren
        | Literal TrueLiteral -> SkipChildren
        | Literal FalseLiteral -> SkipChildren
        | Extract (hi, lo, e) ->
            self#add_tok (pos_of_intval hi) "number";
            self#add_tok (pos_of_intval lo) "number";
            DoChildren
        | ZeroExtend (i, _) ->
            self#add_tok (pos_of_intval i) "number";
            DoChildren
        | SignExtend (i, _) ->
            self#add_tok (pos_of_intval i) "number";
            DoChildren
        | _ -> DoChildren
    end

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
                let pos, id = unpack_blockident id linebreaks in
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
            let pos, ident =
              unpack_ident (bident_of_procident id) linebreaks
            in
            proc_refs <- TokenMap.add pos ident proc_refs)
          r;
        SkipChildren

      method! vdecl (d : declaration) =
        let get_end = function
          | ProcedureDef (spec, bl, blocks, EndList (pos, _)) -> Some pos
          | _ -> None
        in

        (match d with
        | Procedure (ProcedureSig (ProcIdent (b, ident), _, _), attr, def) ->
            let e = get_end def |> function Some e -> e | None -> b in
            let pos, id = unpack_ident (BIdent (b, ident)) linebreaks in
            let pd : def_info =
              {
                label = id;
                label_tok = pos;
                range_start = Token.begin_linecol pos;
                range_end = loc_of_char_pos linebreaks (snd e);
              }
            in
            proc_defs <- StringMap.add id pd proc_defs;
            current_proc <- Some id;
            proc_children <- StringMap.add id [] proc_children
        | _ -> ());
        DoChildren

      method! vblock (b : block) =
        match b with
        | Block1 (id, _, bg, _, _, ed) ->
            let pos, id =
              unpack_ident (bident_of_blockident id) linebreaks
            in
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

  let get_symbs (linebreaks : linebreaks) (p : moduleT) =
    let vis = new getBlocks linebreaks in
    let tvis = new getTokens linebreaks in
    let _ = visit_prog vis p in
    let _ = visit_prog tvis p in
    {
      proc_defs = vis#get_proc_defs;
      proc_children = vis#get_proc_children;
      block_defs = vis#get_block_defs;
      proc_refs = vis#get_proc_refs;
      block_refs = vis#get_block_refs;
      all_tokens = tvis#get_tokens ();
    }
end

let parse (c : in_channel) : AbsBasilIR.moduleT =
  let lexbuf = Lexing.from_channel c in
  try ParBasilIR.pModuleT LexBasilIR.token lexbuf
  with ParBasilIR.Error ->
    let start_pos = Lexing.lexeme_start_p lexbuf
    and end_pos = Lexing.lexeme_end_p lexbuf in
    raise (BNFC_Util.Parse_error (start_pos, end_pos))

let showTree (t : AbsBasilIR.moduleT) : string =
  "[Linearized tree]\n\n"
  ^ PrintBasilIR.printTree PrintBasilIR.prtModuleT t
  ^ "\n"

type doc_ast =
  | SyntaxError of (string * position * position)
  | Ast of AbsBasilIR.moduleT * Processor.symbs

type state_after_processing = {
  linebreaks : linebreaks;
  ast : doc_ast;
  procs : BasilAST.BasilAST.proc list;
  graphs : (unit -> Cfg.procedure_rec) StringMap.t;
}

let process (s : string) : state_after_processing =
  let lexbuf = Lexing.from_string s in
  let linebreaks = Processor.linebreaks s in
  try
    let prog = ParBasilIR.pModuleT LexBasilIR.token lexbuf in
    let syms = Processor.get_symbs linebreaks prog in
    let tokens = SemanticTokensProcessor.lex_tokens_of_string linebreaks s in
    let syms =
      {
        syms with
        all_tokens =
          TokenMap.union (fun i a b -> Some a) syms.all_tokens tokens;
      }
    in
    let procs =
      try BasilAST.BasilASTLoader.transProgram prog
      with exn ->
        let e = Printexc.to_string exn in
        log (Printf.sprintf "%s:\n" e);
        Option.iter Printexc.print_backtrace oc;
        []
    in
    let graphs =
      List.map
        (fun (proc : BasilAST.BasilAST.proc) ->
          (proc.label, fun () -> Cfg.graph_of_proc proc))
        procs
      |> StringMap.of_list
    in
    (*Processor.print_syms syms; *)
    { linebreaks; ast = Ast (prog, syms); procs; graphs }
  with ParBasilIR.Error ->
    let start_pos = Lexing.lexeme_start_p lexbuf
    and end_pos = Lexing.lexeme_end_p lexbuf in
    {
      linebreaks;
      ast = SyntaxError (lexeme lexbuf, start_pos, end_pos);
      procs = [];
      graphs = StringMap.empty;
    }

let process_some_input_file (_file_contents : string) :
    state_after_processing =
  process _file_contents

let diagnostics (_state : state_after_processing) :
    Linol_lsp.Types.Diagnostic.t list =
  match _state.ast with
  | Ast _ -> []
  | SyntaxError (l, p1, p2) ->
      [
        Linol_lsp.Types.Diagnostic.create
          ~message:(`String ("Syntax error: '" ^ l ^ "'"))
          ~range:(range_of_position _state.linebreaks p1 p2)
          ~severity:Linol_lsp.Types.DiagnosticSeverity.Error ();
      ]

open Linol_lwt.Locations
open Linol_lwt

class lsp_server =
  object (self)
    inherit Linol_lwt.Jsonrpc2.server

    val buffers
        : (Linol_lsp.Types.DocumentUri.t, state_after_processing) Hashtbl.t =
      Hashtbl.create 32

    method spawn_query_handler f = Linol_lwt.spawn f
    method! config_definition = Some (`Bool true)

    method! config_code_lens_options =
      Some (Linol_lsp.Lsp.Types.CodeLensOptions.create ())

    method! config_symbol =
      Some
        (`DocumentSymbolOptions
           (DocumentSymbolOptions.create ~label:"symbols"
              ~workDoneProgress:true ()))

    method private _on_doc ~(notify_back : Linol_lwt.Jsonrpc2.notify_back)
        (uri : Linol_lsp.Types.DocumentUri.t) (contents : string) =
      let new_state = process_some_input_file contents in
      Hashtbl.replace buffers uri new_state;
      let diags = diagnostics new_state in
      notify_back#send_diagnostic diags

    method on_notif_doc_did_open ~notify_back d ~content : unit Linol_lwt.t =
      self#_on_doc ~notify_back d.uri content

    method on_notif_doc_did_change ~notify_back d _c ~old_content:_old
        ~new_content =
      self#_on_doc ~notify_back d.uri new_content

    method on_req_hover ~notify_back ~id ~uri ~pos ~workDoneToken
        (d : Linol_lwt.doc_state) =
      Lwt.return None

    method! on_req_code_lens_resolve ~notify_back ~id code_lens =
      (* our code lenses are cheap so probably fine to resolve in one
         stage *)
      Lwt.return code_lens

    method! config_list_commands = [ "show_cfg" ]

    method! on_req_execute_command ~notify_back ~id ~workDoneToken cmd args =
      let proc =
        (match args with
        | Some [ uri; `String proc ] ->
            Some (Linol_lsp.Uri0.t_of_yojson uri, proc)
        | _ -> None)
        |> Option.map (fun (uri, proc_label) ->
               let state = Hashtbl.find buffers uri in
               let pg = StringMap.find proc_label state.graphs in
               let g = pg () in
               Cfg.display_with_viewer g)
      in
      Lwt.return (`String "ok")

    method! on_req_code_lens ~notify_back ~id ~uri ~workDoneToken
        ~partialResultToken ds =
      let state = Hashtbl.find buffers uri in
      let p =
        state.procs
        |> List.map (fun (p : BasilAST.BasilAST.proc) ->
               let b, e = p.label_lexical_range |> Option.get in
               let range =
                 token_of_char_range state.linebreaks b e |> Token.to_range
               in
               let command : Linol_lsp.Types.Command.t =
                 {
                   arguments =
                     Some [ Linol_lsp.Uri0.yojson_of_t uri; `String p.label ];
                   command = "show_cfg";
                   title = "Show CFG";
                 }
               in
               let codelens =
                 Linol_lsp.Types.CodeLens.create ~command ~range ()
               in
               codelens)
      in
      Lwt.return p

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
      let r =
        (match (Hashtbl.find buffers uri).ast with
        | Ast (p, syms) -> Some syms
        | _ -> None)
        |> Option.map (fun s -> Processor.get_syms s)
        |> Option.map (fun x -> `DocumentSymbol x)
      in
      (function Some x -> log "syms" | None -> log "no syms") r;
      Lwt.return r

    method on_notif_doc_did_close ~notify_back:_ d : unit Linol_lwt.t =
      Hashtbl.remove buffers d.uri;
      Linol_lwt.return ()

    method config_modify_capabilities (c : ServerCapabilities.t) :
        ServerCapabilities.t =
      {
        c with
        semanticTokensProvider =
          Some
            (`SemanticTokensRegistrationOptions
               SemanticTokensProcessor.semantic_tokens_config);
      }

    method on_request_unhandled : type r.
        notify_back:Linol_lwt.Jsonrpc2.notify_back ->
        id:Linol_lwt.Jsonrpc2.Req_id.t ->
        r Linol.Lsp.Client_request.t ->
        r Linol_lwt.Jsonrpc2.IO.t =
      fun ~notify_back:(_ : Linol_lwt.Jsonrpc2.notify_back) ~id:_ _r ->
        match _r with
        | Linol_lsp.Client_request.SemanticTokensFull
            { partialResultToken; textDocument; workDoneToken } ->
            let uri = textDocument.uri in
            (match (Hashtbl.find buffers uri).ast with
            | Ast (p, syms) -> Some syms
            | _ -> None)
            |> Option.map (fun s -> Processor.to_semantic_highlight_data s)
            |> fun i -> Lwt.return i
        | _ -> failwith "TODO: handle this\n       request"
  end

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
      Option.iter (fun oc -> Printf.fprintf oc "error: %s\n%!" e) oc;
      exit 1

let () =
  Option.iter
    (fun oc ->
      Printexc.record_backtrace true;
      Printexc.register_printer (function e ->
          Some
            (Printexc.print_backtrace oc;
             "")))
    oc;
  run ()
