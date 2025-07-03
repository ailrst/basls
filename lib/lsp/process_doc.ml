open Common.Util
open Yojson
open Lexing
open Basilloader.BasilVisitor
open Lwt.Infix
open Lsp.Types
open BasilIR
open Basillang
open Tokens
open Semantic_tokens
open Common.Util

let log x = ()

type def_info = {
  label : string;
  label_tok : Token.t;
  range_start : LineCol.t;
  range_end : LineCol.t;
}

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

  let get_semantic_token_map (s : symbs) =
    SemanticTokensProcessor.empty
    |> SemanticTokensProcessor.add (StringMap.to_seq s.proc_defs)
         (fun (_, di) ->
           ( di.label_tok,
             { token_type = "class"; token_modifiers = [ "definition" ] } ))
    |> SemanticTokensProcessor.add (StringMap.to_rev_seq s.block_defs)
         (fun (_, di) ->
           ( di.label_tok,
             { token_type = "method"; token_modifiers = [ "definition" ] } ))
    |> SemanticTokensProcessor.add_tokmap s.block_refs
         { token_type = "method"; token_modifiers = [] }
    |> SemanticTokensProcessor.add_tokmap s.proc_refs
         { token_type = "class"; token_modifiers = [] }
    |> TokenMap.union (fun i a b -> Some a) s.all_tokens

  let to_semantic_highlight_data (s : symbs) =
    SemanticTokensProcessor.to_semantic_tokens_full
      (get_semantic_token_map s)

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
    | BlockIdent ((p1, p2), n) -> (token_of_char_range linebreaks p1 p2, n)

  let unpack_ident id linebreaks =
    match id with (b, e), n -> (token_of_char_range linebreaks b e, n)

  let rec type_idents (t : typeT) =
    match t with
    | TypeBVType (BVType1 (BVTYPE t)) -> [ t ]
    | TypeIntType (IntType1 (INTTYPE t)) -> [ t ]
    | TypeBoolType (BoolType1 (BOOLTYPE t)) -> [ t ]
    | TypeMapType (MapType1 (t1, t2)) -> type_idents t1 @ type_idents t2

  let pos_of_intval t =
    match t with
    | IntVal_Hex (IntegerHex i) -> i
    | IntVal_Dec (IntegerDec i) -> i

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
        | LVar_Local (LocalVar1 (LocalIdent i, t)) ->
            self#add_tok i "variable";
            type_idents t |> List.iter (fun i -> self#add_tok i "type");
            SkipChildren
        | LVar_Global (GlobalVar1 (GlobalIdent i, t)) ->
            self#add_tok i "variable";
            type_idents t |> List.iter (fun i -> self#add_tok i "type");
            SkipChildren

      method! vdecl (p : decl) =
        (match p with
        | Decl_Axiom _ -> ()
        | Decl_ProgEmpty (ProcIdent i, _) ->
            self#add_tok_modifiers i "class" []
        | Decl_ProgWithSpec (ProcIdent i, _, _, _, _) ->
            self#add_tok_modifiers i "class" []
        | Decl_SharedMem (GlobalIdent i, t) ->
            type_idents t |> List.iter (fun i -> self#add_tok i "type");
            self#add_tok_modifiers i "variable" [ "declaration" ]
        | Decl_UnsharedMem (GlobalIdent i, t) ->
            type_idents t |> List.iter (fun i -> self#add_tok i "type");
            self#add_tok_modifiers i "variable" [ "declaration" ]
        | Decl_Var (GlobalIdent i, t) ->
            type_idents t |> List.iter (fun i -> self#add_tok i "type");
            self#add_tok_modifiers i "variable" [ "declaration" ]
        | Decl_UninterpFun (attr, GlobalIdent i, ts, t) ->
            List.concat_map type_idents (t :: ts)
            |> List.iter (fun i -> self#add_tok i "type");
            self#add_tok_modifiers i "function" [ "declaration" ]
        | Decl_Fun (attr, GlobalIdent i, _, t, _) ->
            type_idents t |> List.iter (fun i -> self#add_tok i "type");
            self#add_tok_modifiers i "function" [ "declaration" ]
        | Decl_Proc (ProcIdent i, inparams, outparams, attrib, spec, def) ->
            let of_param = function
              | Params1 (LocalIdent i, t) ->
                  self#add_tok i "parameter";
                  type_idents t |> List.iter (fun i -> self#add_tok i "type")
            in
            List.iter of_param inparams;
            List.iter of_param outparams;
            self#add_tok_modifiers i "class" [ "declaration" ]);
        DoChildren

      method! vstmt (s : stmt) =
        match s with
        | Stmt_Load (lv, _, GlobalIdent i, exp, iv) ->
            self#add_tok (pos_of_intval iv) "number";
            self#add_tok i "variable";
            DoChildren
        | Stmt_Store (_, GlobalIdent i, _, _, iv) ->
            self#add_tok i "variable";
            self#add_tok (pos_of_intval iv) "number";
            DoChildren
        | _ -> DoChildren

      method! vexpr (e : expr) =
        match e with
        | Expr_FunctionOp (GlobalIdent i, p) ->
            self#add_tok i "function";
            DoChildren
        | Expr_Global (GlobalVar1 (GlobalIdent i, t)) ->
            self#add_tok i "variable";
            List.iter (fun i -> self#add_tok i "type") (type_idents t);
            SkipChildren
        | Expr_Local (LocalVar1 (LocalIdent i, t)) ->
            self#add_tok i "variable";
            List.iter (fun i -> self#add_tok i "type") (type_idents t);
            SkipChildren
        | Expr_Literal (Value_Int (IntVal_Hex (IntegerHex i))) ->
            self#add_tok i "number";
            SkipChildren
        | Expr_Literal (Value_Int (IntVal_Dec (IntegerDec i))) ->
            self#add_tok i "number";
            SkipChildren
        | Expr_Literal
            (Value_BV
               (BVVal1 (IntVal_Hex (IntegerHex i), BVType1 (BVTYPE t)))) ->
            self#add_tok i "number";
            self#add_tok t "type";
            SkipChildren
        | Expr_Literal
            (Value_BV
               (BVVal1 (IntVal_Dec (IntegerDec i), BVType1 (BVTYPE t)))) ->
            self#add_tok i "number";
            self#add_tok t "type";
            SkipChildren
        | Expr_Literal Value_True -> SkipChildren
        | Expr_Literal Value_False -> SkipChildren
        | Expr_Extract (hi, lo, e) ->
            self#add_tok (pos_of_intval hi) "number";
            self#add_tok (pos_of_intval lo) "number";
            DoChildren
        | Expr_ZeroExtend (i, _) ->
            self#add_tok (pos_of_intval i) "number";
            DoChildren
        | Expr_SignExtend (i, _) ->
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
        | Jump_GoTo idents ->
            List.iter
              (fun id ->
                let pos, id = unpack_blockident id linebreaks in
                block_refs <- TokenMap.add pos id block_refs)
              idents
        | _ -> ());
        SkipChildren

      method! vstmt (s : stmt) =
        let r =
          match s with
          | Stmt_DirectCall (_, ProcIdent e, _) -> Some e
          | _ -> None
        in
        Option.iter
          (fun ((b, e), ident) ->
            let pos = token_of_char_range linebreaks b e in
            proc_refs <- TokenMap.add pos ident proc_refs)
          r;
        SkipChildren

      method! vdecl (d : decl) =
        let get_end = function
          | ProcDef_Some (bl, blocks, EndList (pos, _)) -> Some pos
          | _ -> None
        in

        (match d with
        | Decl_Proc (ProcIdent b, inparam, outparam, attr, spec, def) ->
            let e = get_end def |> function Some e -> e | None -> fst b in
            let pos, id = unpack_ident b linebreaks in
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
        | Block1 (BlockIdent b, _, bg, _, _, EndList ((beg, _), _)) ->
            let pos, id = unpack_ident b linebreaks in
            let proc = Option.get current_proc in
            let nblocks = id :: StringMap.find proc proc_children in
            let blockdef =
              {
                label = id;
                label_tok = pos;
                range_start = Token.begin_linecol pos;
                range_end = loc_of_char_pos linebreaks beg;
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
