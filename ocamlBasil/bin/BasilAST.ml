open Hashcons

let combine acc n = (acc * 65599) + n
let combine2 acc n1 n2 = combine (combine acc n1) n2

let unquote s =
  if String.starts_with ~prefix:"\"" s && String.ends_with ~suffix:"\"" s
  then String.sub s 1 (String.length s - 2)
  else s

class fresh () =
  object (self)
    val mutable counter = 0

    method get () =
      counter <- counter + 1;
      counter
  end

let fresh = new fresh ()

module BasilAST = struct
  type btype = Bitvector of int | Integer | Boolean | Map of btype * btype
  [@@deriving show, eq]

  type integer = Z.t

  let pp_integer = Z.pp_print
  let show_integer i = Z.to_string i
  let equal_integer i j = Z.equal i j

  type bitvector = int * integer [@@deriving show, eq]

  let bv_size b = fst b
  let bv_val b = snd b

  type endian = LittleEndian | BigEndian [@@deriving show, eq]

  type textRange = (int * int) option [@@deriving show, eq]
  and ident = string * textRange [@@deriving show, eq]

  let string_of_ident i = fst i

  type unOp = BOOLNOT | INTNEG | BVNOT | BVNEG [@@deriving show, eq]

  type binOp =
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

  type expr_node =
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

  and expr = expr_node hash_consed

  let expr_view e = e.node

  type lVar = LVarDef of ident * btype | GlobalLVar of ident * btype
  [@@deriving eq]
  let show_lVar = function 
    | LVarDef (i, t) -> Printf.sprintf "%s: %s" (fst i) (show_btype t)
    | GlobalLVar (i, t) -> Printf.sprintf "%s" (fst i)
  let pp_lVar fmt e = Format.pp_print_string fmt (show_lVar e)


  module ExprHashable = struct
    type t = expr_node

    let equal (e1 : t) (e2 : t) : bool =
      match (e1, e2) with
      | RVar (i, t), RVar (i2, t2) -> i = i2 && t = t2
      | BinaryExpr (bop, e1, e2), BinaryExpr (bop2, e12, e22) ->
          bop = bop2 && e1 == e12 && e2 == e22
      | UnaryExpr (op1, e1), UnaryExpr (op2, e2) -> op1 = op2 && e1 == e2
      | ZeroExtend (sz, e1), ZeroExtend (sz2, e2) -> sz = sz2 && e1 == e2
      | SignExtend (sz, e1), SignExtend (sz2, e2) -> sz = sz2 && e1 == e2
      | Extract (hi1, lo1, e1), Extract (hi2, lo2, e2) ->
          hi1 = hi2 && lo1 = lo2 && e1 == e2
      | Concat (e11, e12), Concat (e21, e22) -> e11 == e21 && e12 == e22
      | BVConst bv1, BVConst bv2 -> equal_bitvector bv1 bv2
      | IntConst i, IntConst i2 -> equal_integer i i2
      | BoolConst i, BoolConst i2 -> i = i2
      | _ -> false

    let hash (e1 : t) : int =
      match e1 with
      | BinaryExpr (bop, e1, e2) -> combine2 (Hashtbl.hash bop) e1.tag e2.tag
      | UnaryExpr (uop, e1) -> combine e1.tag (Hashtbl.hash uop)
      | ZeroExtend (i, e) -> combine e.tag (Hashtbl.hash i)
      | SignExtend (i, e) -> combine e.tag (Hashtbl.hash i)
      | Extract (hi, lo, e) ->
          combine2 e.tag (Hashtbl.hash hi) (Hashtbl.hash lo)
      | Concat (e1, e2) -> combine e1.tag e2.tag
      | RVar (i, t) -> combine (Hashtbl.hash i) (Hashtbl.hash t)
      | BVConst bv ->
          combine (Hashtbl.hash (bv_size bv)) (Z.hash @@ bv_val bv)
      | IntConst i -> Hashtbl.hash i
      | BoolConst b -> Hashtbl.hash b
  end

  module H = Hashcons.Make (ExprHashable)

  let ht = H.create 255
  let cons = H.hashcons ht

  let rec show_expr_node e =
    match e with
    | RVar (i, t) -> Printf.sprintf "%s:%s" (show_ident i) (show_btype t)
    | BinaryExpr (op, e1, e2) ->
        Printf.sprintf "%s(%s, %s)" (show_binOp op) (show_expr e1)
          (show_expr e2)
    | UnaryExpr (op, e2) ->
        Printf.sprintf "%s(%s)" (show_unOp op) (show_expr e2)
    | ZeroExtend (sz, e) ->
        Printf.sprintf "zero_extend(%s, %s)" (show_integer sz) (show_expr e)
    | SignExtend (sz, e) ->
        Printf.sprintf "sign_extend(%s, %s)" (show_integer sz) (show_expr e)
    | Extract (hi, lo, e) ->
        Printf.sprintf "bvextract(%s, %s, %s)" (show_integer hi)
          (show_integer lo) (show_expr e)
    | Concat (e1, e2) ->
        Printf.sprintf "bvconcat(%s, %s)" (show_expr e1) (show_expr e2)
    | BVConst bv -> show_bitvector bv
    | IntConst i -> show_integer i
    | BoolConst true -> "true"
    | BoolConst false -> "false"

  and show_expr e = show_expr_node (expr_view e)

  let pp_expr fmt e = Format.pp_print_string fmt (show_expr e)
  let pp_expr_node fmt e = Format.pp_print_string fmt (show_expr_node e)
  let equal_expr (e1 : expr) (e2 : expr) = e1 == e2
  let compare_expr (e1 : expr) (e2 : expr) = Int.compare e1.tag e2.tag
  let rvar ~name ~typ = cons (RVar (name, typ))

  let rvar_of_lvar l =
    match l with
    | LVarDef (name, typ) -> rvar ~name ~typ
    | GlobalLVar (name, typ) -> rvar ~name ~typ

  let binexp ~op l r = cons (BinaryExpr (op, l, r))
  let unexp ~op arg = cons (UnaryExpr (op, arg))
  let zero_extend ~n_prefix_bits arg = cons (ZeroExtend (n_prefix_bits, arg))
  let sign_extend ~n_prefix_bits arg = cons (SignExtend (n_prefix_bits, arg))

  let bvextract ~hi_incl ~lo_excl arg =
    cons (Extract (hi_incl, lo_excl, arg))

  let bvconcat arg1 arg2 = cons (Concat (arg1, arg2))
  let bvconst bv = cons (BVConst bv)
  let intconst i = cons (IntConst i)
  let boolconst b = cons (BoolConst b)

  type statement =
    | Assign of lVar * expr
    | Load of lVar * endian * ident * expr * integer
    | Store of endian * ident * expr * expr * integer
    | DirectCall of lVar list * ident * expr list
    | IndirectCall of expr
    | Assume of expr
    | Assert of expr
  [@@deriving eq]
  

  let string_of_endian = function 
    | LittleEndian -> "le"
    | BigEndian -> "be"
  let show_statement = function 
    | Assign (v, e) -> Printf.sprintf "%s := %s" (show_lVar v) (show_expr e)
      | Load (lv, endian, mem, addr, sz) -> Printf.sprintf "load %s %s %s %s" (string_of_endian endian) (fst mem) (show_expr addr) (show_integer sz)
      | Store (endian, mem, addr,value, sz) -> Printf.sprintf "store %s %s %s %s %s" (string_of_endian endian) (fst mem) (show_expr addr) (show_expr value) (show_integer sz)
      | DirectCall _ ->  "call"
      | IndirectCall _ ->  "indirect call"
      | Assume e -> Printf.sprintf "assume %s" (show_expr e)
      | Assert e -> Printf.sprintf "assert %s" (show_expr e)
  let pp_statement fmt e = Format.pp_print_string fmt (show_statement e)

  type jump = GoTo of ident list | Unreachable | Return of expr list
  [@@deriving show]

  type block = {
    label : string;
    begin_loc : int;
    stmts : statement list;
    end_loc : int;
    jump : jump;
    addr : integer option;
    label_lexical_range : textRange;
    stmts_lexical_range : textRange;
  }
  [@@deriving show]

  type proc = {
    label : string;
    formal_in_params : lVar list;
    formal_out_params : lVar list;
    addr : integer option;
    entry : string option;
    internal_blocks : block list;
    label_lexical_range : textRange;
    blocklist_lexical_range : textRange;
  }
  [@@deriving show]
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
    match x with BIdent (r, id) -> (unquote id, Some r)

  and transStr (x : str) : string =
    match x with
    | Str string -> unquote string

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
          PD (beginrec, str, paddress, pentry, internalblocks, endrec) ) ->
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
          begin_loc = fresh#get ();
          end_loc = fresh#get ();
          jump = transJump jump;
          label_lexical_range = textrange;
          addr = transAddrAttr addrattr;
          stmts = List.mapi (fun i s -> transStatement s) statements;
          stmts_lexical_range = list_begin_end_to_textrange beginlist endlist;
        }

  and transPEntry (x : pEntry) : string option =
    match x with
    | EntrySome block -> Some (transStr block)
    | EntryNone -> None

  and transPAddress (x : pAddress) : integer option =
    match x with
    | AddrSome intval -> Some (transIntVal intval)
    | AddrNone -> None

  and transInternalBlocks (x : internalBlocks) : block list * textRange =
    match x with
    | BSome (beginlist, blocks, endlist) ->
        ( List.map transBlock blocks,
          list_begin_end_to_textrange beginlist endlist )
    | BNone -> ([], None)

  and param_to_lvar (pp : params) : BasilAST.lVar =
    match pp with Param (id, t) -> LVarDef (transBIdent id, transType t)

  and transParams (x : params) : BasilAST.lVar = param_to_lvar x

  and transExpr (x : BasilIR.AbsBasilIR.expr) : BasilAST.expr =
    match x with
    | RVar (bident, type') ->
        rvar ~name:(transBIdent bident) ~typ:(transType type')
    | BinaryExpr (binop, expr0, expr) ->
        binexp ~op:(transBinOp binop) (transExpr expr0) (transExpr expr)
    | UnaryExpr (unop, expr) -> unexp ~op:(transUnOp unop) (transExpr expr)
    | ZeroExtend (intval, expr) ->
        zero_extend ~n_prefix_bits:(transIntVal intval) (transExpr expr)
    | SignExtend (intval, expr) ->
        sign_extend ~n_prefix_bits:(transIntVal intval) (transExpr expr)
    | Extract (ival0, intval, expr) ->
        bvextract ~hi_incl:(transIntVal ival0) ~lo_excl:(transIntVal intval)
          (transExpr expr)
    | Concat (expr0, expr) -> bvconcat (transExpr expr0) (transExpr expr)
    | BVLiteral (intval, BVT bvtype) ->
        bvconst
          ( (match transBVTYPE bvtype with
            | Bitvector i -> i
            | _ -> failwith "unreachable"),
            transIntVal intval )
    | IntLiteral intval -> intconst (transIntVal intval)
    | TrueLiteral -> boolconst true
    | FalseLiteral -> boolconst false

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
