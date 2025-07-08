open BasilAST

module BasilASTLoader = struct
  open BasilIR.AbsBasilIR
  open BasilAST
  open Helper

  let failure x = failwith "Undefined case." (* x discarded *)

  let rec transBVTYPE (x : bVTYPE) : BasilAST.btype =
    match x with
    | BVTYPE (_, string) ->
        let sz =
          String.split_on_char 'v' string |> function
          | h :: l :: _ -> int_of_string l
          | _ -> failwith "bad bv format"
        in
        Bitvector sz

  and transBIdent (x : bIdent) : ident =
    match x with BIdent (r, id) -> unquote id

  and transStr (x : str) : string =
    match x with Str string -> unquote string

  and transProgram (x : moduleT) : proc list =
    match x with
    | Module1 declarations -> List.concat_map transDeclaration declarations

  and transDeclaration (x : decl) : proc list =
    match x with
    | Decl_SharedMem (bident, type') -> []
    | Decl_UnsharedMem (bident, type') -> []
    | Decl_Var (bident, type') -> []
    | Decl_UninterpFun (attrDefList, glident, argtypes, rettype) -> []
    | Decl_Fun (attrList, glident, params, rt, body) -> []
    | Decl_Axiom _ -> []
    | Decl_ProgEmpty _ -> []
    | Decl_ProgWithSpec _ -> []
    | Decl_Proc (id, inparam, ourparam, attrib, spec, ProcDef_Empty) -> []
    | Decl_Proc
        ( ProcIdent (id_pos, id),
          in_params,
          out_params,
          attrs,
          spec_list,
          ProcDef_Some (bl, blocks, el) ) ->
        let internal_blocks = List.map transBlock blocks in
        let entry =
          match internal_blocks with h :: tl -> Some h.label | _ -> None
        in
        [
          {
            label = id;
            label_lexical_range = Some id_pos;
            formal_in_params = List.map transParams in_params;
            formal_out_params = List.map transParams out_params;
            addr = None;
            entry;
            internal_blocks;
            blocklist_lexical_range = None;
          };
        ]

  and transMapType (x : mapType) : btype =
    match x with MapType1 (t0, t1) -> Map (transType t0, transType t1)

  and transType (x : typeT) : btype =
    match x with
    | TypeIntType inttype -> Integer
    | TypeBoolType booltype -> Boolean
    | TypeMapType maptype -> transMapType maptype
    | TypeBVType (BVType1 bvtype) -> transBVTYPE bvtype

  and transIntVal (x : intVal) : integer =
    match x with
    | IntVal_Hex (IntegerHex (_, ihex)) -> Z.of_string ihex
    | IntVal_Dec (IntegerDec (_, i)) -> Z.of_string i

  and transEndian (x : BasilIR.AbsBasilIR.endian) : BasilAST.endian =
    match x with Endian_Little -> LittleEndian | Endian_Big -> BigEndian

  and transStatement (x : BasilIR.AbsBasilIR.stmtWithAttrib) :
      BasilAST.statement =
    let stmt = match x with StmtWithAttrib1 (stmt, _) -> stmt in
    match stmt with
    | Stmt_SingleAssign (Assignment1 (lvar, expr)) ->
        Assign [ (transLVar lvar, transExpr expr) ]
    | Stmt_MultiAssign assigns ->
        Assign
          (assigns
          |> List.map (function Assignment1 (l, r) ->
                 (transLVar l, transExpr r)))
    | Stmt_Load (lvar, endian, bident, expr, intval) ->
        Load
          ( transLVar lvar,
            transEndian endian,
            unsafe_unsigil (`Global bident),
            transExpr expr,
            transIntVal intval )
    | Stmt_Store (endian, bident, expr0, expr, intval) ->
        Store
          ( transEndian endian,
            unsafe_unsigil (`Global bident),
            transExpr expr0,
            transExpr expr,
            transIntVal intval )
    | Stmt_DirectCall (calllvars, bident, exprs) ->
        DirectCall
          ( transCallLVars calllvars,
            unsafe_unsigil (`Proc bident),
            List.map transExpr exprs )
    | Stmt_IndirectCall expr -> IndirectCall (transExpr expr)
    | Stmt_Assume expr -> Assume (transExpr expr)
    | Stmt_Guard expr -> Assume (transExpr expr)
    | Stmt_Assert expr -> Assert (transExpr expr)

  and transCallLVars (x : lVars) : lVar list =
    match x with
    | LVars_Empty -> []
    | LVars_LocalList lvars ->
        lvars
        |> List.map (function LocalVar1 (i, t) ->
               BasilAST.LVarDef (unsafe_unsigil (`Local i), transType t))
    | LVars_List lvars -> List.map transLVar lvars

  and unpackLVars lvs =
    List.map
      (function
        | LocalVar1 (i, t) -> (unsafe_unsigil (`Local i), transType t))
      lvs

  and transJump (x : BasilIR.AbsBasilIR.jumpWithAttrib) : jump =
    let jump = match x with JumpWithAttrib1 (jump, _) -> jump in
    match jump with
    | Jump_GoTo bidents ->
        GoTo (List.map (fun i -> unsafe_unsigil (`Block i)) bidents)
    | Jump_Unreachable -> Unreachable
    | Jump_Return exprs -> Return (List.map transExpr exprs)

  and transLVar (x : BasilIR.AbsBasilIR.lVar) : BasilAST.lVar =
    match x with
    | LVar_Local (LocalVar1 (bident, type')) ->
        BasilAST.LVarDef (unsafe_unsigil (`Local bident), transType type')
    | LVar_Global (GlobalVar1 (bident, type')) ->
        BasilAST.GlobalLVar (unsafe_unsigil (`Global bident), transType type')

  and list_begin_end_to_textrange beginlist endlist : textRange =
    let beg = match beginlist with BeginList ((i, j), l) -> i in
    let ed = match endlist with EndList ((i, j), l) -> j in
    Some (beg, ed)

  and rec_begin_end_to_textrange beginlist endlist : textRange =
    let beg = match beginlist with BeginRec ((i, j), l) -> i in
    let ed = match endlist with EndRec ((i, j), l) -> j in
    Some (beg, ed)

  and transBlock (x : BasilIR.AbsBasilIR.block) : block =
    match x with
    | Block1
        ( BlockIdent (text_range, name),
          addrattr,
          beginlist,
          statements,
          jump,
          endlist ) ->
        let begin_loc = fresh#get () in
        let end_loc = fresh#get () in
        {
          label = name;
          begin_loc;
          end_loc;
          jump = transJump jump;
          label_lexical_range = Some text_range;
          addr = None;
          stmts = List.mapi (fun i s -> transStatement s) statements;
          stmts_lexical_range = list_begin_end_to_textrange beginlist endlist;
        }

  and param_to_lvar (pp : params) : BasilAST.lVar =
    match pp with
    | Params1 (LocalIdent (pos, id), t) -> LVarDef (id, transType t)

  and transParams (x : params) : BasilAST.lVar = param_to_lvar x

  and unsafe_unsigil g : ident =
    match g with
    | `Global (GlobalIdent (pos, g)) -> g
    | `Local (LocalIdent (pos, g)) -> g
    | `Proc (ProcIdent (pos, g)) -> g
    | `Block (BlockIdent (pos, g)) -> g

  and transExpr (x : BasilIR.AbsBasilIR.expr) : BasilAST.expr =
    match x with
    | Expr_Global (GlobalVar1 (g, type')) ->
        rvar (unsafe_unsigil (`Global g)) ~typ:(transType type')
    | Expr_Local (LocalVar1 (g, type')) ->
        rvar (unsafe_unsigil (`Local g)) ~typ:(transType type')
    | Expr_Binary (binop, expr0, expr) ->
        binexp ~op:(transBinOp binop) (transExpr expr0) (transExpr expr)
    | Expr_Unary (unop, expr) -> unexp ~op:(transUnOp unop) (transExpr expr)
    | Expr_ZeroExtend (intval, expr) ->
        zero_extend
          ~n_prefix_bits:(Z.to_int @@ transIntVal intval)
          (transExpr expr)
    | Expr_SignExtend (intval, expr) ->
        sign_extend
          ~n_prefix_bits:(Z.to_int @@ transIntVal intval)
          (transExpr expr)
    | Expr_Extract (ival0, intval, expr) ->
        bvextract ~hi_incl:(transIntVal ival0) ~lo_excl:(transIntVal intval)
          (transExpr expr)
    | Expr_Concat (expr0, expr) ->
        bvconcat (transExpr expr0) (transExpr expr)
    | Expr_Literal (Value_BV (BVVal1 (intval, BVType1 bvtype))) ->
        bvconst
          ( (match transBVTYPE bvtype with
            | Bitvector i -> i
            | _ -> failwith "unreachable"),
            transIntVal intval )
    | Expr_Literal (Value_Int intval) -> intconst (transIntVal intval)
    | Expr_Literal Value_True -> boolconst true
    | Expr_Literal Value_False -> boolconst false
    | Expr_Old e -> old (transExpr e)
    | Expr_Forall (LambdaDef1 (lv, _, e)) ->
        forall (unpackLVars lv) (transExpr e)
    | Expr_Exists (LambdaDef1 (lv, _, e)) ->
        exists (unpackLVars lv) (transExpr e)
    | Expr_FunctionOp (gi, args) ->
        expr_call (unsafe_unsigil (`Global gi)) (List.map transExpr args)

  and transBinOp (x : BasilIR.AbsBasilIR.binOp) : BasilAST.binOp =
    match x with
    | BinOpBVBinOp bvbinop -> transBVBinOp bvbinop
    | BinOpBVLogicalBinOp bvlogicalbinop ->
        transBVLogicalBinOp bvlogicalbinop
    | BinOpBoolBinOp boolbinop -> transBoolBinOp boolbinop
    | BinOpIntLogicalBinOp intlogicalbinop ->
        transIntLogicalBinOp intlogicalbinop
    | BinOpIntBinOp intbinop -> transIntBinOp intbinop
    | BinOpEqOp equop -> transEqOp equop

  and transUnOp (x : BasilIR.AbsBasilIR.unOp) : unOp =
    match x with
    | UnOpBVUnOp bvunop -> transBVUnOp bvunop
    | UnOp_boolnot -> BOOLNOT
    | UnOp_intneg -> INTNEG
    | UnOp_booltobv1 -> BOOL2BV1

  and transBVUnOp (x : bVUnOp) : unOp =
    match x with BVUnOp_bvnot -> BVNOT | BVUnOp_bvneg -> BVNEG

  and transBVBinOp (x : BasilIR.AbsBasilIR.bVBinOp) : BasilAST.binOp =
    match x with
    | BVBinOp_bvand -> BVAND
    | BVBinOp_bvor -> BVOR
    | BVBinOp_bvadd -> BVADD
    | BVBinOp_bvmul -> BVMUL
    | BVBinOp_bvudiv -> BVUDIV
    | BVBinOp_bvurem -> BVUREM
    | BVBinOp_bvshl -> BVSHL
    | BVBinOp_bvlshr -> BVLSHR
    | BVBinOp_bvnand -> BVNAND
    | BVBinOp_bvnor -> BVNOR
    | BVBinOp_bvxor -> BVXOR
    | BVBinOp_bvxnor -> BVXNOR
    | BVBinOp_bvcomp -> BVCOMP
    | BVBinOp_bvsub -> BVSUB
    | BVBinOp_bvsdiv -> BVSDIV
    | BVBinOp_bvsrem -> BVSREM
    | BVBinOp_bvsmod -> BVSMOD
    | BVBinOp_bvashr -> BVASHR

  and transBVLogicalBinOp (x : bVLogicalBinOp) : binOp =
    match x with
    | BVLogicalBinOp_bvule -> BVULE
    | BVLogicalBinOp_bvult -> BVULT
    | BVLogicalBinOp_bvugt -> BVUGT
    | BVLogicalBinOp_bvuge -> BVUGE
    | BVLogicalBinOp_bvslt -> BVSLT
    | BVLogicalBinOp_bvsle -> BVSLE
    | BVLogicalBinOp_bvsgt -> BVSGT
    | BVLogicalBinOp_bvsge -> BVSGE

  and transEqOp (x : eqOp) : binOp =
    match x with EqOp_eq -> EQ | EqOp_neq -> NEQ

  and transIntBinOp (x : intBinOp) : binOp =
    match x with
    | IntBinOp_intadd -> INTADD
    | IntBinOp_intmul -> INTMUL
    | IntBinOp_intsub -> INTSUB
    | IntBinOp_intdiv -> INTDIV
    | IntBinOp_intmod -> INTMOD

  and transIntLogicalBinOp (x : intLogicalBinOp) : binOp =
    match x with
    | IntLogicalBinOp_intlt -> INTLT
    | IntLogicalBinOp_intle -> INTLE
    | IntLogicalBinOp_intgt -> INTGT
    | IntLogicalBinOp_intge -> INTGE

  and transBoolBinOp (x : boolBinOp) : binOp =
    match x with
    | BoolBinOp_booland -> BOOLAND
    | BoolBinOp_boolor -> BOOLOR
    | BoolBinOp_boolimplies -> BOOLIMPLIES
end

let ast_of_concrete_ast m = BasilASTLoader.transProgram m

let ast_of_channel c =
  let m = Basilloader.Cast_loader.concrete_ast_of_channel c in
  BasilASTLoader.transProgram m
