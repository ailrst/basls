(****************************************************************
 * visitor class
 *
 * This code follows the pattern used in the cilVisitor class in
 * George Necula's excellent CIL (https://people.eecs.berkeley.edu/~necula/cil/)
 * and makes use of the generic Visitor module that is copied from CIL.
 ****************************************************************)

(** ASL visitor class *)

open BasilIR.AbsBasilIR
open Visitor

class type basilVisitor = object
  method vdecl : declaration -> declaration visitAction
  method vprog : moduleT -> moduleT visitAction
  method vproc : procDef -> procDef visitAction
  method vblock : block -> block visitAction
  method vstmt : statement -> statement visitAction
  method vjump : jump -> jump visitAction
  method vtype : typeT -> typeT visitAction
  method vexpr : expr -> expr visitAction
  method vlvar : lVar -> lVar visitAction
end

let singletonVisitAction (a : 'a visitAction) : 'a list visitAction =
  let listpost post : 'a list -> 'a list = function
    | [ x ] -> [ post x ]
    | xs ->
        let len = string_of_int @@ List.length xs in
        failwith
        @@ "this ChangeDoChildrenPost handles single values only, but was \
            given a list of " ^ len ^ " items"
  in
  match a with
  | ChangeTo x -> ChangeTo [ x ]
  | ChangeDoChildrenPost (x, post) ->
      ChangeDoChildrenPost ([ x ], listpost post)
  | DoChildren -> DoChildren
  | SkipChildren -> SkipChildren

let nochildren x y = y

(** a base class for treeVisitors transforming the AST. the method
    visit_stmts is left abstract for subclasses to implement. *)
class virtual basilTreeVisitor (vis : #basilVisitor) =
  object (self)
    method visit_prog (p : moduleT) : moduleT =
      let next _ p =
        match p with
        | Module1 decls -> Module1 (mapNoCopy self#visit_decl decls)
      in
      doVisit vis (vis#vprog p) next p

    method visit_procdef (p : procDef) : procDef =
      let ndef v def =
        match def with
        | ProcedureDecl specList as decl -> decl
        | ProcedureDef (specList, b, blocks, e) ->
            let blocks = mapNoCopy self#visit_block blocks in
            ProcedureDef (specList, b, blocks, e)
      in
      doVisit vis (vis#vproc p) ndef p

    method visit_decl (p : declaration) : declaration =
      let next _ p =
        match p with
        | AxiomDecl _ -> p
        | ProgDecl _ -> p
        | ProgDeclWithSpec _ -> p
        | SharedMemDecl _ -> p
        | UnsharedMemDecl _ -> p
        | VarDecl _ -> p
        | UninterpFunDecl _ -> p
        | FunDef _ -> p
        | Procedure (procSig, attrs, def) ->
            let ndef = self#visit_procdef def in
            Procedure (procSig, attrs, ndef)
      in
      doVisit vis (vis#vdecl p) next p

    method visit_block (b : block) : block =
      let next _ b =
        match b with
        | Block1 (bg, label, addr, stmts, j, ed) ->
            Block1
              ( bg,
                label,
                addr,
                mapNoCopy self#visit_statement stmts,
                self#visit_jump j,
                ed )
      in
      doVisit vis (vis#vblock b) next b

    method visit_statement (s : statement) : statement =
      let next _ b =
        match b with
        | Assign (o, expr) -> Assign (self#visit_lvar o, self#visit_expr expr)
        | SLoad (lVar, endian, memory, addr, size) ->
            let nlv = self#visit_lvar lVar in
            let nadr = self#visit_expr addr in
            if nlv <> lVar || nadr <> addr then
              SLoad (nlv, endian, memory, nadr, size)
            else b
        | SStore (endian, bIdent, addr, value, size) ->
            let nadr = self#visit_expr addr in
            let nvalue = self#visit_expr value in
            if nadr <> addr || nvalue <> value then
              SStore (endian, bIdent, nadr, nvalue, size)
            else b
        | DirectCall (callLVars, bIdent, actual_params) ->
            let params = mapNoCopy self#visit_expr actual_params in
            if params <> actual_params then
              DirectCall (callLVars, bIdent, params)
            else b
        | IndirectCall expr ->
            let ne = self#visit_expr expr in
            if ne <> expr then IndirectCall ne else b
        | Assume expr ->
            let ne = self#visit_expr expr in
            if ne <> expr then Assume ne else b
        | Assert expr ->
            let ne = self#visit_expr expr in
            if ne <> expr then Assert ne else b
      in
      doVisit vis (vis#vstmt s) next s

    method visit_jump (j : jump) : jump =
      let next _ j =
        match j with
        | Return params ->
            let np = mapNoCopy self#visit_expr params in
            if np <> params then Return np else j
        | j -> j
      in
      doVisit vis (vis#vjump j) next j

    method visit_expr (e : expr) =
      let next _ e =
        match e with
        | RVar (bIdent, typeT) -> e
        | BinaryExpr (binOp, l, r) ->
            let nl = self#visit_expr l in
            let nr = self#visit_expr r in
            if nl <> l || nr <> r then BinaryExpr (binOp, nl, nr) else e
        | UnaryExpr (unOp, l) ->
            let nl = self#visit_expr l in
            if nl <> l then UnaryExpr (unOp, l) else e
        | ZeroExtend (intVal, expr) ->
            let nl = self#visit_expr expr in
            if nl <> expr then ZeroExtend (intVal, expr) else e
        | SignExtend (intVal, expr) ->
            let nl = self#visit_expr expr in
            if nl <> expr then SignExtend (intVal, expr) else e
        | Extract (upper, lower, expr) ->
            let nl = self#visit_expr expr in
            if nl <> expr then Extract (upper, lower, expr) else e
        | Concat (l, r) ->
            let nl = self#visit_expr l in
            let nr = self#visit_expr r in
            if nl <> l || nr <> r then Concat (nl, nr) else e
        | BVLiteral (intVal, bVType) -> e
        | IntLiteral intVal -> e
        | TrueLiteral -> e
        | FalseLiteral -> e
      in
      doVisit vis (vis#vexpr e) next e

    method visit_lvar (e : lVar) = doVisit vis (vis#vlvar e) nochildren e

    method visit_type (x : typeT) : typeT =
      doVisit vis (vis#vtype x) nochildren x
  end

class nopBasilVisitor : basilVisitor =
  object
    method vdecl (_ : declaration) = DoChildren
    method vprog (_ : moduleT) = DoChildren
    method vproc (_ : procDef) = DoChildren
    method vblock (_ : block) = DoChildren
    method vstmt (_ : statement) = DoChildren
    method vjump (_ : jump) = DoChildren
    method vtype (_ : typeT) = DoChildren
    method vexpr (_ : expr) = DoChildren
    method vlvar (_ : lVar) = DoChildren
  end

class forwardBasilvisitor (vis : #basilVisitor) =
  object (self)
    inherit basilTreeVisitor vis
  end

let visit_prog (vis : #basilVisitor) (p : moduleT) =
  (new forwardBasilvisitor vis)#visit_prog p

let visit_block (vis : #basilVisitor) (p : block) =
  (new forwardBasilvisitor vis)#visit_block p
