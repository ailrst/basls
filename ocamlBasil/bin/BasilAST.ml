

module BasilAST = struct
  type btype = Bitvector of int | Integer | Boolean | Map of btype * btype
  [@@deriving show, eq]

  type integer = Z.t

  let pp_integer = Z.pp_print
  let show_integer i = Z.to_string i
  let equal_integer i j = Z.equal i j


  type bitvector = int * integer
  [@@deriving show, eq]

  and endian = LittleEndian | BigEndian
  [@@deriving show, eq]

  type textRange = (int * int) option
  [@@deriving show, eq]
  and ident = string * textRange
  [@@deriving show, eq]

  and block = {
    label : string;
    addr : integer option;
    stmts : statement list;
    jump : jump;
    label_lexical_range : textRange;
    stmts_lexical_range : textRange;
  }
  [@@deriving show, eq]

  and proc = {
    label : string;
    formal_in_params : lVar list;
    formal_out_params : lVar list;
    addr : integer option;
    entry : block option;
    exit : block option;
    internal_blocks : block list;
    label_lexical_range : textRange;
    blocklist_lexical_range : textRange;
  }
  [@@deriving show, eq]

  and statement =
    | Assign of lVar * expr
    | Load of lVar * endian * ident * expr * integer
    | Store of endian * ident * expr * expr * integer
    | DirectCall of lVar list * ident * expr list
    | IndirectCall of expr
    | Assume of expr
    | Assert of expr
  [@@deriving show, eq]

  and jump = GoTo of ident list | Unreachable | Return of expr list
  [@@deriving show, eq]
  and lVar = LVarDef of ident * btype | GlobalLVar of ident * btype
  [@@deriving show, eq]

  and expr =
    | RVar of ident * btype
    | BinaryExpr of binOp * expr * expr
    | UnaryExpr of unOp * expr
    | ZeroExtend of integer * expr
    | SignExtend of integer * expr
    | Extract of integer * integer * expr
    | Concat of expr * expr
    | BVConst of bitvector
    | IntConst of integer
    | BoolConst of bool
  [@@deriving show, eq]

  and unOp = BOOLNOT | INTNEG | BVNOT | BVNEG
  [@@deriving show, eq]

  and binOp =
    | BVAND
    | BVOR
    | BVADD
    | BVMUL
    | BVUDIV
    | BVUREM
    | BVSHL
    | BVLSHR
    | BVULT
    | BVNAND
    | BVNOR
    | BVXOR
    | BVXNOR
    | BVCOMP
    | BVSUB
    | BVSDIV
    | BVSREM
    | BVSMOD
    | BVASHR
    | BVULE
    | BVUGT
    | BVUGE
    | BVSLT
    | BVSLE
    | BVSGT
    | BVSGE
    | BVEQ
    | BVNEQ
    | INTADD
    | INTMUL
    | INTSUB
    | INTDIV
    | INTMOD
    | INTEQ
    | INTNEQ
    | INTLT
    | INTLE
    | INTGT
    | INTGE
    | BOOLEQ
    | BOOLNEQ
    | BOOLAND
    | BOOLOR
    | BOOLIMPLIES
  [@@deriving show, eq]
end

module BasilASTLoader = struct
  open BasilIR.AbsBasilIR
  open BasilAST

  let oc = open_out "logger1"

  type result = string

  let failure x = failwith "Undefined case." (* x discarded *)

  let rec transBVTYPE (x : bVTYPE) : BasilAST.btype =
    match x with
    | BVTYPE string ->
        let sz =
          String.split_on_char 'v' string |> function
          | h :: l :: _ -> int_of_string l
          | _ -> failwith "bad bv format"
        in
        Bitvector sz

  and transBIdent (x : bIdent) : ident =
    match x with BIdent (r, id) -> (id, Some r)


  and transStr (x : str) : string = match x with Str string -> string

  and transProgram (x : program) : proc list =
    match x with
    | Prog declarations -> List.concat_map transDeclaration declarations

  and transDeclaration (x : declaration) : proc list =
    match x with
    | LetDecl (bident, mexpr) -> []
    | MemDecl (bident, type') -> []
    | VarDecl (bident, type') -> []
    | Procedure
        ( bident,
          paramss0,
          paramss,
          PD (beginrec, str, paddress, pentry, pexit, internalblocks, endrec)
        ) ->
        let id, tr = transBIdent bident in
        let iblocks, blockrange = transInternalBlocks internalblocks in
        [
          {
            label = id;
            label_lexical_range = tr;
            formal_in_params = List.map transParams paramss0;
            formal_out_params = List.map transParams paramss;
            addr = transPAddress paddress;
            entry = transPEntry pentry;
            exit = transPExit pexit;
            internal_blocks = iblocks;
            blocklist_lexical_range = blockrange;
          };
        ]

  and transMapType (x : mapType) : btype =
    match x with
    | MapT (t0, beginlist, t1, endlist) -> Map (transType t0, transType t1)

  and transType (x : typeT) : btype =
    match x with
    | TypeIntType inttype -> Integer
    | TypeBoolType booltype -> Boolean
    | TypeMapType maptype -> transMapType maptype
    | TypeBVType (BVT bvtype) -> transBVTYPE bvtype

  and transIntVal (x : intVal) : integer =
    match x with
    | HexInt (IntegerHex ihex) -> Z.of_string ihex
    | DecInt i -> Z.of_int i

  and transAddrAttr (x : addrAttr) : integer option =
    match x with
    | AddrAttrSome (beginrec, intval, endrec) -> Some (transIntVal intval)
    | AddrAttrNone -> None
    | AddrAttrEmpty (beginrec, endrec) -> None

  and transEndian (x : BasilIR.AbsBasilIR.endian) : BasilAST.endian =
    match x with LittleEndian -> LittleEndian | BigEndian -> BigEndian

  and transStatement (x : BasilIR.AbsBasilIR.statement) : BasilAST.statement
      =
    match x with
    | Assign (lvar, expr) -> Assign (transLVar lvar, transExpr expr)
    | SLoad (lvar, endian, bident, expr, intval) ->
        Load
          ( transLVar lvar,
            transEndian endian,
            transBIdent bident,
            transExpr expr,
            transIntVal intval )
    | SStore (endian, bident, expr0, expr, intval) ->
        Store
          ( transEndian endian,
            transBIdent bident,
            transExpr expr0,
            transExpr expr,
            transIntVal intval )
    | DirectCall (calllvars, bident, exprs) ->
        DirectCall
          ( transCallLVars calllvars,
            transBIdent bident,
            List.map transExpr exprs )
    | IndirectCall expr -> IndirectCall (transExpr expr)
    | Assume expr -> Assume (transExpr expr)
    | Assert expr -> Assert (transExpr expr)

  and transCallLVars (x : callLVars) : lVar list =
    match x with
    | NoOutParams -> []
    | LocalVars lvars ->
        List.map
          (function
            | BasilIR.AbsBasilIR.GlobalLVar (i, t) ->
                transLVar (BasilIR.AbsBasilIR.LVarDef (i, t))
            | t -> transLVar t)
          lvars
    | ListOutParams lvars -> List.map transLVar lvars

  and transJump (x : BasilIR.AbsBasilIR.jump) : jump =
    match x with
    | GoTo bidents -> GoTo (List.map transBIdent bidents)
    | Unreachable -> Unreachable
    | Return exprs -> Return (List.map transExpr exprs)

  and transLVar (x : BasilIR.AbsBasilIR.lVar) : BasilAST.lVar =
    match x with
    | LVarDef (bident, type') ->
        BasilAST.LVarDef (transBIdent bident, transType type')
    | GlobalLVar (bident, type') ->
        BasilAST.GlobalLVar (transBIdent bident, transType type')

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
    | B (bident, addrattr, beginlist, statements, jump, endlist) ->
        let name, textrange = transBIdent bident in
        {
          label = name;
          addr = transAddrAttr addrattr;
          jump = transJump jump;
          label_lexical_range = textrange;
          stmts = (List.mapi (fun i s -> transStatement s) statements);
          stmts_lexical_range = list_begin_end_to_textrange beginlist endlist;
        } 
  and transPEntry (x : pEntry) : block option =
    match x with
    | EntrySome block -> Some (transBlock block)
    | EntryNone -> None

  and transPExit (x : pExit) : block option =
    match x with ESome block -> Some (transBlock block) | ENone -> None

  and transPAddress (x : pAddress) : integer option =
    match x with
    | AddrSome intval -> Some (transIntVal intval)
    | AddrNone -> None

  and transInternalBlocks (x : internalBlocks) : block list * textRange =
    match x with
    | BSome (beginlist, blocks, endlist) ->
        (List.map transBlock blocks,
          list_begin_end_to_textrange beginlist endlist )
    | BNone -> ([], None)

  and param_to_lvar (pp : params) : BasilAST.lVar =
    match pp with Param (id, t) -> LVarDef (transBIdent id, transType t)

  and transParams (x : params) : BasilAST.lVar = param_to_lvar x

  and transExpr (x : BasilIR.AbsBasilIR.expr) : BasilAST.expr =
    match x with
    | RVar (bident, type') -> RVar (transBIdent bident, transType type')
    | BinaryExpr (binop, expr0, expr) ->
        BinaryExpr (transBinOp binop, transExpr expr0, transExpr expr)
    | UnaryExpr (unop, expr) -> UnaryExpr (transUnOp unop, transExpr expr)
    | ZeroExtend (intval, expr) ->
        ZeroExtend (transIntVal intval, transExpr expr)
    | SignExtend (intval, expr) ->
        SignExtend (transIntVal intval, transExpr expr)
    | Extract (ival0, intval, expr) ->
        Extract (transIntVal ival0, transIntVal intval, transExpr expr)
    | Concat (expr0, expr) -> Concat (transExpr expr0, transExpr expr)
    | BVLiteral (intval, BVT bvtype) ->
        BVConst
          ( (match transBVTYPE bvtype with
            | Bitvector i -> i
            | _ -> failwith "unreachable"),
            transIntVal intval )
    | IntLiteral intval -> IntConst (transIntVal intval)
    | TrueLiteral -> BoolConst true
    | FalseLiteral -> BoolConst false

  and transBinOp (x : BasilIR.AbsBasilIR.binOp) : BasilAST.binOp =
    match x with
    | BinOpBVBinOp bvbinop -> transBVBinOp bvbinop
    | BinOpBVLogicalBinOp bvlogicalbinop ->
        transBVLogicalBinOp bvlogicalbinop
    | BinOpBoolBinOp boolbinop -> transBoolBinOp boolbinop
    | BinOpIntLogicalBinOp intlogicalbinop ->
        transIntLogicalBinOp intlogicalbinop
    | BinOpIntBinOp intbinop -> transIntBinOp intbinop

  and transUnOp (x : BasilIR.AbsBasilIR.unOp) : unOp =
    match x with
    | UnOpBVUnOp bvunop -> transBVUnOp bvunop
    | UnOp_boolnot -> BOOLNOT
    | UnOp_intneg -> INTNEG

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
    | BVBinOp_bvult -> BVULT
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
    | BVLogicalBinOp_bvugt -> BVUGT
    | BVLogicalBinOp_bvuge -> BVUGE
    | BVLogicalBinOp_bvslt -> BVSLT
    | BVLogicalBinOp_bvsle -> BVSLE
    | BVLogicalBinOp_bvsgt -> BVSGT
    | BVLogicalBinOp_bvsge -> BVSGE
    | BVLogicalBinOp_bveq -> BVEQ
    | BVLogicalBinOp_bvneq -> BVNEQ

  and transIntBinOp (x : intBinOp) : binOp =
    match x with
    | IntBinOp_intadd -> INTADD
    | IntBinOp_intmul -> INTMUL
    | IntBinOp_intsub -> INTSUB
    | IntBinOp_intdiv -> INTDIV
    | IntBinOp_intmod -> INTMOD

  and transIntLogicalBinOp (x : intLogicalBinOp) : binOp =
    match x with
    | IntLogicalBinOp_inteq -> INTEQ
    | IntLogicalBinOp_intneq -> INTNEQ
    | IntLogicalBinOp_intlt -> INTLT
    | IntLogicalBinOp_intle -> INTLE
    | IntLogicalBinOp_intgt -> INTGT
    | IntLogicalBinOp_intge -> INTGE

  and transBoolBinOp (x : boolBinOp) : binOp =
    match x with
    | BoolBinOp_booleq -> BOOLEQ
    | BoolBinOp_boolneq -> BOOLNEQ
    | BoolBinOp_booland -> BOOLAND
    | BoolBinOp_boolor -> BOOLOR
    | BoolBinOp_boolimplies -> BOOLIMPLIES
    | BoolBinOp_boolequiv -> BOOLEQ
end
