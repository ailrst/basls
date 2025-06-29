open Hashcons

let combine acc n = (acc * 65599) + n
let combine2 acc n1 n2 = combine (combine acc n1) n2

let rec combinel acc n1 =
  match n1 with [] -> acc | h :: tl -> combinel (combine acc h) tl

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
  type btype =
    | Bitvector of int
    | Integer
    | Boolean
    | Map of btype * btype
    | Top
  [@@deriving eq]

  let rec show_btype = function
    | Bitvector b -> Printf.sprintf "bv%d" b
    | Integer -> "int"
    | Map (k, v) -> "map " ^ show_btype v ^ "[" ^ show_btype k ^ "]"
    | Boolean -> "bool"
    | Top -> "(internal)top"

  type integer = Z.t

  let pp_integer = Z.pp_print
  let show_integer i = Z.to_string i
  let equal_integer i j = Z.equal i j

  type bitvector = int * integer [@@deriving eq]

  let bv_size b = fst b
  let bv_val b = snd b

  let show_bitvector (b : bitvector) =
    Printf.sprintf "0x%s:bv%d" (Z.format "%x" @@ bv_val b) (bv_size b)

  let pp_bitvector fmt b = Format.pp_print_string fmt (show_bitvector b)

  type endian = LittleEndian | BigEndian
  [@@deriving show { with_path = false }, eq]

  type textRange = (int * int) option
  [@@deriving show { with_path = false }, eq]

  and ident = string [@@deriving eq]

  let show_ident (i : ident) : string = i
  let pp_ident fmt i = Format.pp_print_string fmt (show_ident i)

  type unOp = BOOLNOT | INTNEG | BVNOT | BVNEG | BOOL2BV1
  [@@deriving show { with_path = false }, eq]

  let show_unOp x = String.lowercase_ascii (show_unOp x)
  let pp_unOp fmt x = Format.pp_print_string fmt (show_unOp x)

  type binOp =
    | EQ
    | NEQ
    | BVAND
    | BVOR
    | BVADD
    | BVMUL
    | BVUDIV
    | BVUREM
    | BVSHL
    | BVLSHR
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
    | BVULT
    | BVULE
    | BVUGT
    | BVUGE
    | BVSLT
    | BVSLE
    | BVSGT
    | BVSGE
    | INTADD
    | INTMUL
    | INTSUB
    | INTDIV
    | INTMOD
    | INTLT
    | INTLE
    | INTGT
    | INTGE
    | BOOLAND
    | BOOLOR
    | BOOLIMPLIES
  [@@deriving show { with_path = false }, eq]

  let binop_is_int = function
    | INTADD | INTMUL | INTSUB | INTDIV | INTMOD -> true
    | BOOLIMPLIES | BVULT | BVULE | BVUGT | BVUGE | BVSLT | BVSLE | BVSGT
    | BVSGE | INTLT | INTLE | INTGT | INTGE | BOOLAND | BOOLOR | BVAND | BVOR
    | BVADD | BVMUL | BVUDIV | BVUREM | BVSHL | BVLSHR | BVNAND | BVNOR
    | BVXOR | BVXNOR | BVCOMP | BVSUB | BVSDIV | BVSREM | BVSMOD | BVASHR
    | EQ | NEQ ->
        false

  let binop_is_bv = function
    | BVAND | BVOR | BVADD | BVMUL | BVUDIV | BVUREM | BVSHL | BVLSHR
    | BVNAND | BVNOR | BVXOR | BVXNOR | BVCOMP | BVSUB | BVSDIV | BVSREM
    | BVSMOD | BVASHR ->
        true
    | BVULT | BVULE | BVUGT | BVUGE | BVSLT | BVSLE | BVSGT | BVSGE | INTADD
    | INTMUL | INTSUB | INTDIV | INTMOD | INTLT | INTLE | INTGT | INTGE
    | BOOLAND | BOOLOR | BOOLIMPLIES | EQ | NEQ ->
        false

  let binop_is_pred = function
    | BVULT | BVULE | BVUGT | BVUGE | BVSLT | BVSLE | BVSGT | BVSGE | INTLT
    | INTLE | INTGT | INTGE | BOOLAND | BOOLOR | EQ | NEQ | BOOLIMPLIES ->
        true
    | BVAND | BVOR | BVADD | BVMUL | BVUDIV | BVUREM | BVSHL | BVLSHR
    | BVNAND | BVNOR | BVXOR | BVXNOR | BVCOMP | BVSUB | BVSDIV | BVSREM
    | BVSMOD | BVASHR | INTADD | INTMUL | INTSUB | INTDIV | INTMOD ->
        false

  let bool_expr =
    [
      EQ;
      NEQ;
      INTLT;
      INTLE;
      INTGT;
      INTGE;
      BOOLAND;
      BOOLOR;
      BOOLIMPLIES;
      BVULT;
      BVULE;
      BVUGT;
      BVUGE;
      BVSLT;
      BVSLE;
      BVSGT;
      BVSGE;
    ]

  let show_binOp x = String.lowercase_ascii (show_binOp x)
  let pp_binOp fmt x = Format.pp_print_string fmt (show_binOp x)

  type expr_node =
    | RVar of ident * btype * int
    | BinaryExpr of binOp * expr * expr
    | UnaryExpr of unOp * expr
    | ZeroExtend of int * expr
    | SignExtend of int * expr
    | Extract of integer * integer * expr
    | Concat of expr * expr
    | BVConst of bitvector
    | IntConst of integer
    | BoolConst of bool
    | Old of expr
    | Forall of (ident * btype) list * expr
    | Exists of (ident * btype) list * expr
    | ExprCall of ident * expr list * btype

  and expr = expr_node hash_consed

  let expr_view e = e.node
  let expr_tag e = e.tag

  let rec expr_type e =
    (* This is inefficient, (but could be efficiently memoised with hash
       consing) We store just enough information to reconstruct the type
       locally; only atom exprs (rvars and constants) store their type *)
    match expr_view e with
    | RVar (_, t, _) -> t
    | BinaryExpr (o, l, r) when binop_is_int o -> Integer
    | BinaryExpr (o, l, r) when binop_is_pred o -> Boolean
    | BinaryExpr (o, l, r) when binop_is_bv o -> expr_type l
    | BinaryExpr (BVCOMP, l, r) -> Bitvector 1
    | BinaryExpr (o, l, r) -> failwith "should be matched by guarded clause"
    | BVConst bv -> Bitvector (bv_size bv)
    | IntConst _ -> Integer
    | BoolConst _ -> Boolean
    | UnaryExpr (BOOLNOT, _) -> Boolean
    | UnaryExpr (INTNEG, _) -> Integer
    | UnaryExpr (BVNEG, x) -> Bitvector (bv_width x)
    | UnaryExpr (BVNOT, x) -> Bitvector (bv_width x)
    | UnaryExpr (BOOL2BV1, x) -> Bitvector 1
    | Concat (x, y) -> Bitvector (bv_width x + bv_width y)
    | ZeroExtend (sz, e) -> Bitvector (sz + bv_width e)
    | SignExtend (sz, e) -> Bitvector (sz + bv_width e)
    | Extract (hi, lo, _) -> Bitvector (Z.sub hi lo |> Z.to_int)
    | Forall _ -> Boolean
    | Exists _ -> Boolean
    | Old x -> expr_type x
    | ExprCall (_, _, t) -> t

  and bv_width (e : expr) =
    match expr_type e with
    | Bitvector sz -> sz
    | _ -> failwith "type error; not a bv"

  (* BOOLNOT | INTNEG | BVNOT | BVNEG *)

  type lVar = LVarDef of ident * btype | GlobalLVar of ident * btype
  [@@deriving eq]

  let ident_of_lvar = function LVarDef (v, t) -> v | GlobalLVar (v, t) -> v
  let type_of_lvar = function LVarDef (v, t) -> t | GlobalLVar (v, t) -> t

  let show_lVar = function
    | LVarDef (i, t) -> Printf.sprintf "%s: %s" i (show_btype t)
    | GlobalLVar (i, t) -> Printf.sprintf "%s" i

  let pp_lVar fmt e = Format.pp_print_string fmt (show_lVar e)

  module ExprHashable = struct
    type t = expr_node

    let equal (e1 : t) (e2 : t) : bool =
      match (e1, e2) with
      | RVar (i, t, ind), RVar (i2, t2, ind2) ->
          i = i2 && t = t2 && ind = ind2
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
      | RVar (i, t, ind) ->
          combine2 (Hashtbl.hash i) (Hashtbl.hash t) (Hashtbl.hash ind)
      | BVConst bv ->
          combine (Hashtbl.hash (bv_size bv)) (Z.hash @@ bv_val bv)
      | IntConst i -> Hashtbl.hash i
      | BoolConst b -> Hashtbl.hash b
      | Old b -> Hashtbl.hash b.tag
      | Forall (params, b) -> Hashtbl.hash b.tag
      | Exists (params, b) -> Hashtbl.hash b.tag
      | ExprCall (id, params, rt) ->
          combinel (Hashtbl.hash id) (List.map (fun i -> i.tag) params)
  end

  module H = Hashcons.Make (ExprHashable)

  let ht = H.create 255
  let cons = H.hashcons ht

  let rec show_expr_node e =
    match e with
    | RVar (i, t, ind) ->
        if ind <> 0 then Printf.sprintf "%s_%d" (show_ident i) ind
        else show_ident i
    | BinaryExpr (op, e1, e2) ->
        Printf.sprintf "%s(%s, %s)" (show_binOp op) (show_expr e1)
          (show_expr e2)
    | UnaryExpr (op, e2) ->
        Printf.sprintf "%s(%s)" (show_unOp op) (show_expr e2)
    | ZeroExtend (sz, e) ->
        Printf.sprintf "zero_extend(%d, %s)" sz (show_expr e)
    | SignExtend (sz, e) ->
        Printf.sprintf "sign_extend(%d, %s)" sz (show_expr e)
    | Extract (hi, lo, e) ->
        Printf.sprintf "bvextract(%s, %s, %s)" (show_integer hi)
          (show_integer lo) (show_expr e)
    | Concat (e1, e2) ->
        Printf.sprintf "bvconcat(%s, %s)" (show_expr e1) (show_expr e2)
    | BVConst bv -> show_bitvector bv
    | IntConst i -> show_integer i
    | BoolConst true -> "true"
    | BoolConst false -> "false"
    | Forall (pl, b) ->
        Printf.sprintf "forall (%s) :: %s"
          (String.concat ", "
             (List.map
                (fun (i, t) ->
                  Printf.sprintf "%s:%s" (show_ident i) (show_btype t))
                pl))
          (show_expr b)
    | Exists (pl, b) ->
        Printf.sprintf "exists (%s) :: %s"
          (String.concat ", "
             (List.map
                (fun (i, t) ->
                  Printf.sprintf "%s:%s" (show_ident i) (show_btype t))
                pl))
          (show_expr b)
    | ExprCall (i, pl, b) ->
        Printf.sprintf "%s (%s) : %s" i
          (String.concat ", "
             (List.map (fun i -> Printf.sprintf "%s" (show_expr i)) pl))
          (show_btype b)
    | Old e -> Printf.sprintf "old(%s)" (show_expr e)

  and show_expr e = show_expr_node (expr_view e)

  let pp_expr fmt e = Format.pp_print_string fmt (show_expr e)
  let pp_expr_node fmt e = Format.pp_print_string fmt (show_expr_node e)
  let equal_expr (e1 : expr) (e2 : expr) = e1 == e2
  let compare_expr (e1 : expr) (e2 : expr) = Int.compare e1.tag e2.tag
  let rvar ?(index = 0) name ~typ = cons (RVar (name, typ, index))

  let rvar_of_lvar l =
    match l with
    | LVarDef (name, typ) -> rvar name ~typ
    | GlobalLVar (name, typ) -> rvar name ~typ

  let binexp ~op l r = cons (BinaryExpr (op, l, r))
  let unexp ~op arg = cons (UnaryExpr (op, arg))
  let zero_extend ~n_prefix_bits arg = cons (ZeroExtend (n_prefix_bits, arg))
  let sign_extend ~n_prefix_bits arg = cons (SignExtend (n_prefix_bits, arg))
  let old e = cons (Old e)
  let forall params e = cons (Forall (params, e))
  let exists params e = cons (Exists (params, e))

  let expr_call id ?(return_type = Top) params =
    cons (ExprCall (id, params, return_type))

  let bvextract ~hi_incl ~lo_excl arg =
    cons (Extract (hi_incl, lo_excl, arg))

  let bvconcat arg1 arg2 = cons (Concat (arg1, arg2))
  let bvconst bv = cons (BVConst bv)
  let intconst i = cons (IntConst i)
  let boolconst b = cons (BoolConst b)

  type statement =
    | Assign of (lVar * expr) list
    | Load of lVar * endian * ident * expr * integer
    | Store of endian * ident * expr * expr * integer
    | DirectCall of lVar list * ident * expr list
    | IndirectCall of expr
    | Assume of expr
    | Assert of expr
  [@@deriving eq]

  let string_of_endian = function LittleEndian -> "le" | BigEndian -> "be"

  let show_statement = function
    | Assign assigns ->
        assigns
        |> List.map (fun (v, e) ->
               Printf.sprintf "%s := %s" (show_lVar v) (show_expr e))
        |> String.concat " | "
    | Load (lv, endian, mem, addr, sz) ->
        Printf.sprintf "%s := load %s %s %s %s" (show_lVar lv)
          (string_of_endian endian) mem (show_expr addr) (show_integer sz)
    | Store (endian, mem, addr, value, sz) ->
        Printf.sprintf "store %s %s %s %s %s" (string_of_endian endian) mem
          (show_expr addr) (show_expr value) (show_integer sz)
    | DirectCall _ -> "call"
    | IndirectCall _ -> "indirect call"
    | Assume e -> Printf.sprintf "assume %s" (show_expr e)
    | Assert e -> Printf.sprintf "assert %s" (show_expr e)

  let pp_statement fmt e = Format.pp_print_string fmt (show_statement e)

  type jump = GoTo of ident list | Unreachable | Return of expr list
  [@@deriving show { with_path = false }]

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
  [@@deriving show { with_path = false }]

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
  [@@deriving show { with_path = false }]
end

module BasilASTLoader = struct
  open BasilIR.AbsBasilIR
  open BasilAST

  let oc = open_out "logger1"
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
    match x with BIdent (r, id) -> unquote id

  and transStr (x : str) : string =
    match x with Str string -> unquote string

  and transProgram (x : moduleT) : proc list =
    match x with
    | Module1 declarations -> List.concat_map transDeclaration declarations

  and transDeclaration (x : declaration) : proc list =
    match x with
    | SharedMemDecl (bident, type') -> []
    | UnsharedMemDecl (bident, type') -> []
    | VarDecl (bident, type') -> []
    | UninterpFunDecl (attrDefList, glident, argtypes, rettype) -> []
    | FunDef (attrList, glident, params, rt, body) -> []
    | AxiomDecl _ -> []
    | ProgDecl _ -> []
    | ProgDeclWithSpec _ -> []
    | Procedure
        ( ProcedureSig (id, in_params, out_params),
          attrs,
          ProcedureDecl spec_list ) ->
        []
    | Procedure
        ( ProcedureSig (ProcIdent (id_pos, id), in_params, out_params),
          attrs,
          ProcedureDef (spec_list, bl, blocks, el) ) ->
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
    match x with MapT (t0, t1) -> Map (transType t0, transType t1)

  and transType (x : typeT) : btype =
    match x with
    | TypeIntType inttype -> Integer
    | TypeBoolType booltype -> Boolean
    | TypeMapType maptype -> transMapType maptype
    | TypeBVType (BVT bvtype) -> transBVTYPE bvtype

  and transIntVal (x : intVal) : integer =
    match x with
    | HexInt (IntegerHex ihex) -> Z.of_string ihex
    | DecInt (IntegerDec i) -> Z.of_string i

  and transEndian (x : BasilIR.AbsBasilIR.endian) : BasilAST.endian =
    match x with LittleEndian -> LittleEndian | BigEndian -> BigEndian

  and transStatement (x : BasilIR.AbsBasilIR.statement) : BasilAST.statement
      =
    match x with
    | Assign (Assignment1 (lvar, expr)) ->
        Assign [ (transLVar lvar, transExpr expr) ]
    | SimulAssign assigns ->
        Assign
          (assigns
          |> List.map (function Assignment1 (l, r) ->
                 (transLVar l, transExpr r)))
    | SLoad (lvar, endian, bident, expr, intval) ->
        Load
          ( transLVar lvar,
            transEndian endian,
            unsafe_unsigil (`Global bident),
            transExpr expr,
            transIntVal intval )
    | SStore (endian, bident, expr0, expr, intval) ->
        Store
          ( transEndian endian,
            unsafe_unsigil (`Global bident),
            transExpr expr0,
            transExpr expr,
            transIntVal intval )
    | DirectCall (calllvars, bident, exprs) ->
        DirectCall
          ( transCallLVars calllvars,
            unsafe_unsigil (`Proc bident),
            List.map transExpr exprs )
    | IndirectCall expr -> IndirectCall (transExpr expr)
    | Assume (expr, _) -> Assume (transExpr expr)
    | Guard (expr, _) -> Assume (transExpr expr)
    | Assert (expr, _) -> Assert (transExpr expr)

  and transCallLVars (x : callLVars) : lVar list =
    match x with
    | NoOutParams -> []
    | LocalVars lvars ->
        lvars
        |> List.map (function LocalVar1 (i, t) ->
               BasilAST.LVarDef (unsafe_unsigil (`Local i), transType t))
    | ListOutParams lvars -> List.map transLVar lvars

  and unpackLVars lvs =
    List.map
      (function
        | LocalVar1 (i, t) -> (unsafe_unsigil (`Local i), transType t))
      lvs

  and transJump (x : BasilIR.AbsBasilIR.jump) : jump =
    match x with
    | GoTo bidents ->
        GoTo (List.map (fun i -> unsafe_unsigil (`Block i)) bidents)
    | Unreachable -> Unreachable
    | Return exprs -> Return (List.map transExpr exprs)

  and transLVar (x : BasilIR.AbsBasilIR.lVar) : BasilAST.lVar =
    match x with
    | LVarDef (LocalVar1 (bident, type')) ->
        BasilAST.LVarDef (unsafe_unsigil (`Local bident), transType type')
    | GlobalLVar (GlobalVar1 (bident, type')) ->
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
    | Param (LocalIdent (pos, id), t) -> LVarDef (id, transType t)

  and transParams (x : params) : BasilAST.lVar = param_to_lvar x

  and unsafe_unsigil g : ident =
    match g with
    | `Global (GlobalIdent (pos, g)) -> g
    | `Local (LocalIdent (pos, g)) -> g
    | `Proc (ProcIdent (pos, g)) -> g
    | `Block (BlockIdent (pos, g)) -> g

  and transExpr (x : BasilIR.AbsBasilIR.expr) : BasilAST.expr =
    match x with
    | GRVar (GlobalVar1 (g, type')) ->
        rvar (unsafe_unsigil (`Global g)) ~typ:(transType type')
    | LRVar (LocalVar1 (g, type')) ->
        rvar (unsafe_unsigil (`Local g)) ~typ:(transType type')
    | BinaryExpr (binop, expr0, expr) ->
        binexp ~op:(transBinOp binop) (transExpr expr0) (transExpr expr)
    | UnaryExpr (unop, expr) -> unexp ~op:(transUnOp unop) (transExpr expr)
    | ZeroExtend (intval, expr) ->
        zero_extend
          ~n_prefix_bits:(Z.to_int @@ transIntVal intval)
          (transExpr expr)
    | SignExtend (intval, expr) ->
        sign_extend
          ~n_prefix_bits:(Z.to_int @@ transIntVal intval)
          (transExpr expr)
    | Extract (ival0, intval, expr) ->
        bvextract ~hi_incl:(transIntVal ival0) ~lo_excl:(transIntVal intval)
          (transExpr expr)
    | Concat (expr0, expr) -> bvconcat (transExpr expr0) (transExpr expr)
    | Literal (BVLiteral (BV (intval, BVT bvtype))) ->
        bvconst
          ( (match transBVTYPE bvtype with
            | Bitvector i -> i
            | _ -> failwith "unreachable"),
            transIntVal intval )
    | Literal (IntLiteral intval) -> intconst (transIntVal intval)
    | Literal TrueLiteral -> boolconst true
    | Literal FalseLiteral -> boolconst false
    | OldExpr e -> old (transExpr e)
    | Forall (LambdaDef1 (lv, _, e)) -> forall (unpackLVars lv) (transExpr e)
    | Exists (LambdaDef1 (lv, _, e)) -> exists (unpackLVars lv) (transExpr e)
    | FunctionOp (gi, args) ->
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
