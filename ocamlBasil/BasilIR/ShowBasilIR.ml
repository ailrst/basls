(* File generated by the BNF Converter (bnfc 2.9.5). *)

(* show functions *)

(* use string buffers for efficient string concatenations *)
type showable = Buffer.t -> unit

let show (s : showable) : string =
    let init_size = 16 in (* you may want to adjust this *)
    let b = Buffer.create init_size in
    s b;
    Buffer.contents b

let emptyS : showable = fun buf -> ()

let c2s (c:char) : showable = fun buf -> Buffer.add_char buf c
let s2s (s:string) : showable = fun buf -> Buffer.add_string buf s

let ( >> ) (s1 : showable) (s2 : showable) : showable = fun buf -> s1 buf; s2 buf

let showChar (c:char) : showable = fun buf ->
    Buffer.add_string buf ("'" ^ Char.escaped c ^ "'")

let showString (s:string) : showable = fun buf ->
    Buffer.add_string buf ("\"" ^ String.escaped s ^ "\"")

let showList (showFun : 'a -> showable) (xs : 'a list) : showable = fun buf ->
    let rec f ys = match ys with
        [] -> ()
      | [y] -> showFun y buf
      | y::ys -> showFun y buf; Buffer.add_string buf "; "; f ys
    in
        Buffer.add_char buf '[';
        f xs;
        Buffer.add_char buf ']'


let showInt (i:int) : showable = s2s (string_of_int i)
let showFloat (f:float) : showable = s2s (string_of_float f)

let rec showBVTYPE (AbsBasilIR.BVTYPE i) : showable = s2s "BVTYPE " >> showString i
let rec showBIdent (AbsBasilIR.BIdent (_,i)) : showable = s2s "BIdent " >> showString i
let rec showStr (AbsBasilIR.Str i) : showable = s2s "Str " >> showString i
let rec showIntegerHex (AbsBasilIR.IntegerHex i) : showable = s2s "IntegerHex " >> showString i

let rec showProgram (e : AbsBasilIR.program) : showable = match e with
       AbsBasilIR.Prog declarations -> s2s "Prog" >> c2s ' ' >> c2s '(' >> showList showDeclaration declarations >> c2s ')'


and showDeclaration (e : AbsBasilIR.declaration) : showable = match e with
       AbsBasilIR.LetDecl (bident, mexpr) -> s2s "LetDecl" >> c2s ' ' >> c2s '(' >> showBIdent bident  >> s2s ", " >>  showMExpr mexpr >> c2s ')'
  |    AbsBasilIR.MemDecl (bident, type') -> s2s "MemDecl" >> c2s ' ' >> c2s '(' >> showBIdent bident  >> s2s ", " >>  showTypeT type' >> c2s ')'
  |    AbsBasilIR.VarDecl (bident, type') -> s2s "VarDecl" >> c2s ' ' >> c2s '(' >> showBIdent bident  >> s2s ", " >>  showTypeT type' >> c2s ')'
  |    AbsBasilIR.Procedure (bident, paramss0, paramss, procdef) -> s2s "Procedure" >> c2s ' ' >> c2s '(' >> showBIdent bident  >> s2s ", " >>  showList showParams paramss0  >> s2s ", " >>  showList showParams paramss  >> s2s ", " >>  showProcDef procdef >> c2s ')'


and showMExpr (e : AbsBasilIR.mExpr) : showable = match e with
       AbsBasilIR.MSym bident -> s2s "MSym" >> c2s ' ' >> c2s '(' >> showBIdent bident >> c2s ')'
  |    AbsBasilIR.BlockM block -> s2s "BlockM" >> c2s ' ' >> c2s '(' >> showBlock block >> c2s ')'


and showIntType (e : AbsBasilIR.intType) : showable = match e with
       AbsBasilIR.IntT  -> s2s "IntT"


and showBoolType (e : AbsBasilIR.boolType) : showable = match e with
       AbsBasilIR.BoolT  -> s2s "BoolT"


and showMapType (e : AbsBasilIR.mapType) : showable = match e with
       AbsBasilIR.MapT (type'0, type') -> s2s "MapT" >> c2s ' ' >> c2s '(' >> showTypeT type'0  >> s2s ", " >>  showTypeT type' >> c2s ')'


and showBVType (e : AbsBasilIR.bVType) : showable = match e with
       AbsBasilIR.ShortBVT bvtype -> s2s "ShortBVT" >> c2s ' ' >> c2s '(' >> showBVTYPE bvtype >> c2s ')'
  |    AbsBasilIR.BitvectorType intlit -> s2s "BitvectorType" >> c2s ' ' >> c2s '(' >> showIntLit intlit >> c2s ')'


and showTypeT (e : AbsBasilIR.typeT) : showable = match e with
       AbsBasilIR.TypeIntType inttype -> s2s "TypeIntType" >> c2s ' ' >> c2s '(' >> showIntType inttype >> c2s ')'
  |    AbsBasilIR.TypeBoolType booltype -> s2s "TypeBoolType" >> c2s ' ' >> c2s '(' >> showBoolType booltype >> c2s ')'
  |    AbsBasilIR.TypeMapType maptype -> s2s "TypeMapType" >> c2s ' ' >> c2s '(' >> showMapType maptype >> c2s ')'
  |    AbsBasilIR.TypeBVType bvtype -> s2s "TypeBVType" >> c2s ' ' >> c2s '(' >> showBVType bvtype >> c2s ')'


and showIntLit (e : AbsBasilIR.intLit) : showable = match e with
       AbsBasilIR.HexInt integerhex -> s2s "HexInt" >> c2s ' ' >> c2s '(' >> showIntegerHex integerhex >> c2s ')'
  |    AbsBasilIR.DecInt integer -> s2s "DecInt" >> c2s ' ' >> c2s '(' >> showInt integer >> c2s ')'


and showAddrAttr (e : AbsBasilIR.addrAttr) : showable = match e with
       AbsBasilIR.AddrAttrSome intlit -> s2s "AddrAttrSome" >> c2s ' ' >> c2s '(' >> showIntLit intlit >> c2s ')'
  |    AbsBasilIR.AddrAttrNone  -> s2s "AddrAttrNone"
  |    AbsBasilIR.AddrAttrEmpty  -> s2s "AddrAttrEmpty"


and showEndian (e : AbsBasilIR.endian) : showable = match e with
       AbsBasilIR.LittleEndian  -> s2s "LittleEndian"
  |    AbsBasilIR.BigEndian  -> s2s "BigEndian"


and showStatement (e : AbsBasilIR.statement) : showable = match e with
       AbsBasilIR.AssignStmt assign -> s2s "AssignStmt" >> c2s ' ' >> c2s '(' >> showAssign assign >> c2s ')'
  |    AbsBasilIR.SLoad (bvlvar, endian, bident, bvexpr, intlit) -> s2s "SLoad" >> c2s ' ' >> c2s '(' >> showBVLVar bvlvar  >> s2s ", " >>  showEndian endian  >> s2s ", " >>  showBIdent bident  >> s2s ", " >>  showBVExpr bvexpr  >> s2s ", " >>  showIntLit intlit >> c2s ')'
  |    AbsBasilIR.SStore (endian, bident, expr, bvexpr, intlit) -> s2s "SStore" >> c2s ' ' >> c2s '(' >> showEndian endian  >> s2s ", " >>  showBIdent bident  >> s2s ", " >>  showExpr expr  >> s2s ", " >>  showBVExpr bvexpr  >> s2s ", " >>  showIntLit intlit >> c2s ')'
  |    AbsBasilIR.DirectCall (bident, exprs) -> s2s "DirectCall" >> c2s ' ' >> c2s '(' >> showBIdent bident  >> s2s ", " >>  showList showExpr exprs >> c2s ')'
  |    AbsBasilIR.DirectCallReturnLocal (lvars, bident, exprs) -> s2s "DirectCallReturnLocal" >> c2s ' ' >> c2s '(' >> showList showLVar lvars  >> s2s ", " >>  showBIdent bident  >> s2s ", " >>  showList showExpr exprs >> c2s ')'
  |    AbsBasilIR.DirectCallReturn (lvars, bident, exprs) -> s2s "DirectCallReturn" >> c2s ' ' >> c2s '(' >> showList showLVar lvars  >> s2s ", " >>  showBIdent bident  >> s2s ", " >>  showList showExpr exprs >> c2s ')'
  |    AbsBasilIR.IndirectCall expr -> s2s "IndirectCall" >> c2s ' ' >> c2s '(' >> showExpr expr >> c2s ')'
  |    AbsBasilIR.Assume expr -> s2s "Assume" >> c2s ' ' >> c2s '(' >> showExpr expr >> c2s ')'
  |    AbsBasilIR.Assert expr -> s2s "Assert" >> c2s ' ' >> c2s '(' >> showExpr expr >> c2s ')'


and showAssign (e : AbsBasilIR.assign) : showable = match e with
       AbsBasilIR.IntAssign (intlvar, intexpr) -> s2s "IntAssign" >> c2s ' ' >> c2s '(' >> showIntLVar intlvar  >> s2s ", " >>  showIntExpr intexpr >> c2s ')'
  |    AbsBasilIR.BVAssign (bvlvar, bvexpr) -> s2s "BVAssign" >> c2s ' ' >> c2s '(' >> showBVLVar bvlvar  >> s2s ", " >>  showBVExpr bvexpr >> c2s ')'
  |    AbsBasilIR.BoolAssign (boollvar, logexpr) -> s2s "BoolAssign" >> c2s ' ' >> c2s '(' >> showBoolLVar boollvar  >> s2s ", " >>  showLogExpr logexpr >> c2s ')'


and showJump (e : AbsBasilIR.jump) : showable = match e with
       AbsBasilIR.GoTo bidents -> s2s "GoTo" >> c2s ' ' >> c2s '(' >> showList showBIdent bidents >> c2s ')'
  |    AbsBasilIR.Unreachable  -> s2s "Unreachable"
  |    AbsBasilIR.Return exprs -> s2s "Return" >> c2s ' ' >> c2s '(' >> showList showExpr exprs >> c2s ')'


and showLVar (e : AbsBasilIR.lVar) : showable = match e with
       AbsBasilIR.LVarIntLVar intlvar -> s2s "LVarIntLVar" >> c2s ' ' >> c2s '(' >> showIntLVar intlvar >> c2s ')'
  |    AbsBasilIR.LVarBVLVar bvlvar -> s2s "LVarBVLVar" >> c2s ' ' >> c2s '(' >> showBVLVar bvlvar >> c2s ')'
  |    AbsBasilIR.LVarBoolLVar boollvar -> s2s "LVarBoolLVar" >> c2s ' ' >> c2s '(' >> showBoolLVar boollvar >> c2s ')'


and showBVLVar (e : AbsBasilIR.bVLVar) : showable = match e with
       AbsBasilIR.LocalBVLVar (bident, bvtype) -> s2s "LocalBVLVar" >> c2s ' ' >> c2s '(' >> showBIdent bident  >> s2s ", " >>  showBVType bvtype >> c2s ')'
  |    AbsBasilIR.GlobalBVLVar (bident, bvtype) -> s2s "GlobalBVLVar" >> c2s ' ' >> c2s '(' >> showBIdent bident  >> s2s ", " >>  showBVType bvtype >> c2s ')'


and showIntLVar (e : AbsBasilIR.intLVar) : showable = match e with
       AbsBasilIR.LocalIntLVar (bident, inttype) -> s2s "LocalIntLVar" >> c2s ' ' >> c2s '(' >> showBIdent bident  >> s2s ", " >>  showIntType inttype >> c2s ')'
  |    AbsBasilIR.GlobalIntLVar (bident, inttype) -> s2s "GlobalIntLVar" >> c2s ' ' >> c2s '(' >> showBIdent bident  >> s2s ", " >>  showIntType inttype >> c2s ')'


and showBoolLVar (e : AbsBasilIR.boolLVar) : showable = match e with
       AbsBasilIR.LocalBoolLVar (bident, booltype) -> s2s "LocalBoolLVar" >> c2s ' ' >> c2s '(' >> showBIdent bident  >> s2s ", " >>  showBoolType booltype >> c2s ')'
  |    AbsBasilIR.GlobalBoolLVar (bident, booltype) -> s2s "GlobalBoolLVar" >> c2s ' ' >> c2s '(' >> showBIdent bident  >> s2s ", " >>  showBoolType booltype >> c2s ')'


and showBlock (e : AbsBasilIR.block) : showable = match e with
       AbsBasilIR.B (bident, addrattr, statements, jump) -> s2s "B" >> c2s ' ' >> c2s '(' >> showBIdent bident  >> s2s ", " >>  showAddrAttr addrattr  >> s2s ", " >>  showList showStatement statements  >> s2s ", " >>  showJump jump >> c2s ')'


and showPEntry (e : AbsBasilIR.pEntry) : showable = match e with
       AbsBasilIR.EntrySome block -> s2s "EntrySome" >> c2s ' ' >> c2s '(' >> showBlock block >> c2s ')'
  |    AbsBasilIR.EntryNone  -> s2s "EntryNone"


and showPExit (e : AbsBasilIR.pExit) : showable = match e with
       AbsBasilIR.ESome block -> s2s "ESome" >> c2s ' ' >> c2s '(' >> showBlock block >> c2s ')'
  |    AbsBasilIR.ENone  -> s2s "ENone"


and showPAddress (e : AbsBasilIR.pAddress) : showable = match e with
       AbsBasilIR.AddrSome intlit -> s2s "AddrSome" >> c2s ' ' >> c2s '(' >> showIntLit intlit >> c2s ')'
  |    AbsBasilIR.AddrNone  -> s2s "AddrNone"


and showInternalBlocks (e : AbsBasilIR.internalBlocks) : showable = match e with
       AbsBasilIR.BSome blocks -> s2s "BSome" >> c2s ' ' >> c2s '(' >> showList showBlock blocks >> c2s ')'
  |    AbsBasilIR.BNone  -> s2s "BNone"


and showProcDef (e : AbsBasilIR.procDef) : showable = match e with
       AbsBasilIR.PD (str, paddress, pentry, pexit, internalblocks) -> s2s "PD" >> c2s ' ' >> c2s '(' >> showStr str  >> s2s ", " >>  showPAddress paddress  >> s2s ", " >>  showPEntry pentry  >> s2s ", " >>  showPExit pexit  >> s2s ", " >>  showInternalBlocks internalblocks >> c2s ')'


and showParams (e : AbsBasilIR.params) : showable = match e with
       AbsBasilIR.Param (bident, type') -> s2s "Param" >> c2s ' ' >> c2s '(' >> showBIdent bident  >> s2s ", " >>  showTypeT type' >> c2s ')'


and showExpr (e : AbsBasilIR.expr) : showable = match e with
       AbsBasilIR.BitvectorExpr bvexpr -> s2s "BitvectorExpr" >> c2s ' ' >> c2s '(' >> showBVExpr bvexpr >> c2s ')'
  |    AbsBasilIR.LogicalExpr logexpr -> s2s "LogicalExpr" >> c2s ' ' >> c2s '(' >> showLogExpr logexpr >> c2s ')'
  |    AbsBasilIR.IntegerExpr intexpr -> s2s "IntegerExpr" >> c2s ' ' >> c2s '(' >> showIntExpr intexpr >> c2s ')'


and showBVExpr (e : AbsBasilIR.bVExpr) : showable = match e with
       AbsBasilIR.BVBinary (bvbinop, bvexpr0, bvexpr) -> s2s "BVBinary" >> c2s ' ' >> c2s '(' >> showBVBinOp bvbinop  >> s2s ", " >>  showBVExpr bvexpr0  >> s2s ", " >>  showBVExpr bvexpr >> c2s ')'
  |    AbsBasilIR.BVUnary (bvunop, bvexpr) -> s2s "BVUnary" >> c2s ' ' >> c2s '(' >> showBVUnOp bvunop  >> s2s ", " >>  showBVExpr bvexpr >> c2s ')'
  |    AbsBasilIR.ZeroExtend (intlit, bvexpr) -> s2s "ZeroExtend" >> c2s ' ' >> c2s '(' >> showIntLit intlit  >> s2s ", " >>  showBVExpr bvexpr >> c2s ')'
  |    AbsBasilIR.SignExtend (intlit, bvexpr) -> s2s "SignExtend" >> c2s ' ' >> c2s '(' >> showIntLit intlit  >> s2s ", " >>  showBVExpr bvexpr >> c2s ')'
  |    AbsBasilIR.Extract (intlit0, intlit, bvexpr) -> s2s "Extract" >> c2s ' ' >> c2s '(' >> showIntLit intlit0  >> s2s ", " >>  showIntLit intlit  >> s2s ", " >>  showBVExpr bvexpr >> c2s ')'
  |    AbsBasilIR.Concat (bvexpr0, bvexpr) -> s2s "Concat" >> c2s ' ' >> c2s '(' >> showBVExpr bvexpr0  >> s2s ", " >>  showBVExpr bvexpr >> c2s ')'
  |    AbsBasilIR.BVLiteral (intlit, bvtype) -> s2s "BVLiteral" >> c2s ' ' >> c2s '(' >> showIntLit intlit  >> s2s ", " >>  showBVType bvtype >> c2s ')'
  |    AbsBasilIR.RBVVar bvrvar -> s2s "RBVVar" >> c2s ' ' >> c2s '(' >> showBVRVar bvrvar >> c2s ')'


and showIntExpr (e : AbsBasilIR.intExpr) : showable = match e with
       AbsBasilIR.IntLiteral intlit -> s2s "IntLiteral" >> c2s ' ' >> c2s '(' >> showIntLit intlit >> c2s ')'
  |    AbsBasilIR.RIntVar intrvar -> s2s "RIntVar" >> c2s ' ' >> c2s '(' >> showIntRVar intrvar >> c2s ')'
  |    AbsBasilIR.IntBinary (intbinop, intexpr0, intexpr) -> s2s "IntBinary" >> c2s ' ' >> c2s '(' >> showIntBinOp intbinop  >> s2s ", " >>  showIntExpr intexpr0  >> s2s ", " >>  showIntExpr intexpr >> c2s ')'
  |    AbsBasilIR.IntNeg intexpr -> s2s "IntNeg" >> c2s ' ' >> c2s '(' >> showIntExpr intexpr >> c2s ')'


and showLogExpr (e : AbsBasilIR.logExpr) : showable = match e with
       AbsBasilIR.BVLogBinary (bvlogicalbinop, bvexpr0, bvexpr) -> s2s "BVLogBinary" >> c2s ' ' >> c2s '(' >> showBVLogicalBinOp bvlogicalbinop  >> s2s ", " >>  showBVExpr bvexpr0  >> s2s ", " >>  showBVExpr bvexpr >> c2s ')'
  |    AbsBasilIR.RLogVar boolrvar -> s2s "RLogVar" >> c2s ' ' >> c2s '(' >> showBoolRVar boolrvar >> c2s ')'
  |    AbsBasilIR.BoolLit boolliteral -> s2s "BoolLit" >> c2s ' ' >> c2s '(' >> showBoolLiteral boolliteral >> c2s ')'
  |    AbsBasilIR.IntLogBinary (intlogicalbinop, intexpr0, intexpr) -> s2s "IntLogBinary" >> c2s ' ' >> c2s '(' >> showIntLogicalBinOp intlogicalbinop  >> s2s ", " >>  showIntExpr intexpr0  >> s2s ", " >>  showIntExpr intexpr >> c2s ')'
  |    AbsBasilIR.BoolLogBinOp (boolbinop, logexpr0, logexpr) -> s2s "BoolLogBinOp" >> c2s ' ' >> c2s '(' >> showBoolBinOp boolbinop  >> s2s ", " >>  showLogExpr logexpr0  >> s2s ", " >>  showLogExpr logexpr >> c2s ')'
  |    AbsBasilIR.BoolNot logexpr -> s2s "BoolNot" >> c2s ' ' >> c2s '(' >> showLogExpr logexpr >> c2s ')'


and showIntRVar (e : AbsBasilIR.intRVar) : showable = match e with
       AbsBasilIR.IRV (bident, inttype) -> s2s "IRV" >> c2s ' ' >> c2s '(' >> showBIdent bident  >> s2s ", " >>  showIntType inttype >> c2s ')'


and showBVRVar (e : AbsBasilIR.bVRVar) : showable = match e with
       AbsBasilIR.BVRV (bident, bvtype) -> s2s "BVRV" >> c2s ' ' >> c2s '(' >> showBIdent bident  >> s2s ", " >>  showBVType bvtype >> c2s ')'


and showBoolRVar (e : AbsBasilIR.boolRVar) : showable = match e with
       AbsBasilIR.BRV (bident, booltype) -> s2s "BRV" >> c2s ' ' >> c2s '(' >> showBIdent bident  >> s2s ", " >>  showBoolType booltype >> c2s ')'


and showBoolLiteral (e : AbsBasilIR.boolLiteral) : showable = match e with
       AbsBasilIR.BoolLiteral_true  -> s2s "BoolLiteral_true"
  |    AbsBasilIR.BoolLiteral_false  -> s2s "BoolLiteral_false"


and showBVUnOp (e : AbsBasilIR.bVUnOp) : showable = match e with
       AbsBasilIR.BVUnOp_bvnot  -> s2s "BVUnOp_bvnot"
  |    AbsBasilIR.BVUnOp_bvneg  -> s2s "BVUnOp_bvneg"


and showBVBinOp (e : AbsBasilIR.bVBinOp) : showable = match e with
       AbsBasilIR.BVBinOp_bvand  -> s2s "BVBinOp_bvand"
  |    AbsBasilIR.BVBinOp_bvor  -> s2s "BVBinOp_bvor"
  |    AbsBasilIR.BVBinOp_bvadd  -> s2s "BVBinOp_bvadd"
  |    AbsBasilIR.BVBinOp_bvmul  -> s2s "BVBinOp_bvmul"
  |    AbsBasilIR.BVBinOp_bvudiv  -> s2s "BVBinOp_bvudiv"
  |    AbsBasilIR.BVBinOp_bvurem  -> s2s "BVBinOp_bvurem"
  |    AbsBasilIR.BVBinOp_bvshl  -> s2s "BVBinOp_bvshl"
  |    AbsBasilIR.BVBinOp_bvlshr  -> s2s "BVBinOp_bvlshr"
  |    AbsBasilIR.BVBinOp_bvnand  -> s2s "BVBinOp_bvnand"
  |    AbsBasilIR.BVBinOp_bvnor  -> s2s "BVBinOp_bvnor"
  |    AbsBasilIR.BVBinOp_bvxor  -> s2s "BVBinOp_bvxor"
  |    AbsBasilIR.BVBinOp_bvxnor  -> s2s "BVBinOp_bvxnor"
  |    AbsBasilIR.BVBinOp_bvcomp  -> s2s "BVBinOp_bvcomp"
  |    AbsBasilIR.BVBinOp_bvsub  -> s2s "BVBinOp_bvsub"
  |    AbsBasilIR.BVBinOp_bvsdiv  -> s2s "BVBinOp_bvsdiv"
  |    AbsBasilIR.BVBinOp_bvsrem  -> s2s "BVBinOp_bvsrem"
  |    AbsBasilIR.BVBinOp_bvsmod  -> s2s "BVBinOp_bvsmod"
  |    AbsBasilIR.BVBinOp_bvashr  -> s2s "BVBinOp_bvashr"


and showBVLogicalBinOp (e : AbsBasilIR.bVLogicalBinOp) : showable = match e with
       AbsBasilIR.BVLogicalBinOp_bvule  -> s2s "BVLogicalBinOp_bvule"
  |    AbsBasilIR.BVLogicalBinOp_bvugt  -> s2s "BVLogicalBinOp_bvugt"
  |    AbsBasilIR.BVLogicalBinOp_bvuge  -> s2s "BVLogicalBinOp_bvuge"
  |    AbsBasilIR.BVLogicalBinOp_bvslt  -> s2s "BVLogicalBinOp_bvslt"
  |    AbsBasilIR.BVLogicalBinOp_bvsle  -> s2s "BVLogicalBinOp_bvsle"
  |    AbsBasilIR.BVLogicalBinOp_bvsgt  -> s2s "BVLogicalBinOp_bvsgt"
  |    AbsBasilIR.BVLogicalBinOp_bvsge  -> s2s "BVLogicalBinOp_bvsge"
  |    AbsBasilIR.BVLogicalBinOp_bveq  -> s2s "BVLogicalBinOp_bveq"
  |    AbsBasilIR.BVLogicalBinOp_bvneq  -> s2s "BVLogicalBinOp_bvneq"
  |    AbsBasilIR.BVLogicalBinOp_bvult  -> s2s "BVLogicalBinOp_bvult"


and showIntBinOp (e : AbsBasilIR.intBinOp) : showable = match e with
       AbsBasilIR.IntBinOp_intadd  -> s2s "IntBinOp_intadd"
  |    AbsBasilIR.IntBinOp_intmul  -> s2s "IntBinOp_intmul"
  |    AbsBasilIR.IntBinOp_intsub  -> s2s "IntBinOp_intsub"
  |    AbsBasilIR.IntBinOp_intdiv  -> s2s "IntBinOp_intdiv"
  |    AbsBasilIR.IntBinOp_intmod  -> s2s "IntBinOp_intmod"


and showIntLogicalBinOp (e : AbsBasilIR.intLogicalBinOp) : showable = match e with
       AbsBasilIR.IntLogicalBinOp_inteq  -> s2s "IntLogicalBinOp_inteq"
  |    AbsBasilIR.IntLogicalBinOp_intneq  -> s2s "IntLogicalBinOp_intneq"
  |    AbsBasilIR.IntLogicalBinOp_intlt  -> s2s "IntLogicalBinOp_intlt"
  |    AbsBasilIR.IntLogicalBinOp_intle  -> s2s "IntLogicalBinOp_intle"
  |    AbsBasilIR.IntLogicalBinOp_intgt  -> s2s "IntLogicalBinOp_intgt"
  |    AbsBasilIR.IntLogicalBinOp_intge  -> s2s "IntLogicalBinOp_intge"


and showBoolBinOp (e : AbsBasilIR.boolBinOp) : showable = match e with
       AbsBasilIR.BoolBinOp_booleq  -> s2s "BoolBinOp_booleq"
  |    AbsBasilIR.BoolBinOp_boolneq  -> s2s "BoolBinOp_boolneq"
  |    AbsBasilIR.BoolBinOp_booland  -> s2s "BoolBinOp_booland"
  |    AbsBasilIR.BoolBinOp_boolor  -> s2s "BoolBinOp_boolor"
  |    AbsBasilIR.BoolBinOp_boolimplies  -> s2s "BoolBinOp_boolimplies"
  |    AbsBasilIR.BoolBinOp_boolequiv  -> s2s "BoolBinOp_boolequiv"



