(****************************************************************
 * visitor class
 *
 * This code follows the pattern used in the cilVisitor class in
 * George Necula's excellent CIL (https://people.eecs.berkeley.edu/~necula/cil/)
 * and makes use of the generic Visitor module that is copied from CIL.
 ****************************************************************)

(** ASL visitor class *)

open BasilIR.AbsBasilIR
open Common.Visitor

class type basilVisitor = object
  method vdecl : decl -> decl visitAction
  method vprog : moduleT -> moduleT visitAction
  method vproc : procDef -> procDef visitAction
  method vblock : block -> block visitAction
  method vstmt : stmt -> stmt visitAction
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
        | ProcDef_Empty as decl -> decl
        | ProcDef_Some (beginList, blocks, endList) ->
            let blocks = mapNoCopy self#visit_block blocks in
            ProcDef_Some (beginList, blocks, endList)
      in
      doVisit vis (vis#vproc p) ndef p

    method visit_decl (p : decl) : decl =
      let next _ p =
        match p with
        | Decl_Axiom _ -> p
        | Decl_ProgEmpty _ -> p
        | Decl_ProgWithSpec _ -> p
        | Decl_SharedMem _ -> p
        | Decl_UnsharedMem _ -> p
        | Decl_Var _ -> p
        | Decl_UninterpFun _ -> p
        | Decl_Fun _ -> p
        | Decl_Proc (pident, inparam, outparam, attrs, specs, def) ->
            let def = self#visit_procdef def in
            Decl_Proc (pident, inparam, outparam, attrs, specs, def)
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
                mapNoCopy self#visit_stmt stmts,
                self#visit_jump j,
                ed )
      in
      doVisit vis (vis#vblock b) next b

    method visit_stmt (s : stmt) : stmt =
      let next _ b =
        match b with
        | Stmt_SingleAssign (Assignment1 (o, expr)) ->
            Stmt_SingleAssign
              (Assignment1 (self#visit_lvar o, self#visit_expr expr))
        | Stmt_MultiAssign alist ->
            Stmt_MultiAssign
              (List.map
                 (function
                   | Assignment1 (o, expr) ->
                       Assignment1 (self#visit_lvar o, self#visit_expr expr))
                 alist)
        | Stmt_Load (lVar, endian, memory, addr, size) ->
            let nlv = self#visit_lvar lVar in
            let nadr = self#visit_expr addr in
            if nlv <> lVar || nadr <> addr then
              Stmt_Load (nlv, endian, memory, nadr, size)
            else b
        | Stmt_Store (endian, bIdent, addr, value, size) ->
            let nadr = self#visit_expr addr in
            let nvalue = self#visit_expr value in
            if nadr <> addr || nvalue <> value then
              Stmt_Store (endian, bIdent, nadr, nvalue, size)
            else b
        | Stmt_DirectCall (callLVars, bIdent, actual_params) ->
            let params = mapNoCopy self#visit_expr actual_params in
            if params <> actual_params then
              Stmt_DirectCall (callLVars, bIdent, params)
            else b
        | Stmt_IndirectCall expr ->
            let ne = self#visit_expr expr in
            if ne <> expr then Stmt_IndirectCall ne else b
        | Stmt_Assume (expr, attr) ->
            let ne = self#visit_expr expr in
            if ne <> expr then Stmt_Assume (ne, attr) else b
        | Stmt_Guard (expr, attr) ->
            let ne = self#visit_expr expr in
            if ne <> expr then Stmt_Guard (ne, attr) else b
        | Stmt_Assert (expr, attr) ->
            let ne = self#visit_expr expr in
            if ne <> expr then Stmt_Assert (ne, attr) else b
      in
      doVisit vis (vis#vstmt s) next s

    method visit_jump (j : jump) : jump =
      let next _ j =
        match j with
        | Jump_Return params ->
            let np = mapNoCopy self#visit_expr params in
            if np <> params then Jump_Return np else j
        | j -> j
      in
      doVisit vis (vis#vjump j) next j

    method visit_expr (e : expr) =
      let next _ e =
        match e with
        | Expr_Global rvar -> e
        | Expr_Local rvar -> e
        | Expr_Binary (binOp, l, r) ->
            let nl = self#visit_expr l in
            let nr = self#visit_expr r in
            if nl <> l || nr <> r then Expr_Binary (binOp, nl, nr) else e
        | Expr_Unary (unOp, l) ->
            let nl = self#visit_expr l in
            if nl <> l then Expr_Unary (unOp, l) else e
        | Expr_ZeroExtend (intVal, expr) ->
            let nl = self#visit_expr expr in
            if nl <> expr then Expr_ZeroExtend (intVal, expr) else e
        | Expr_SignExtend (intVal, expr) ->
            let nl = self#visit_expr expr in
            if nl <> expr then Expr_SignExtend (intVal, expr) else e
        | Expr_Extract (upper, lower, expr) ->
            let nl = self#visit_expr expr in
            if nl <> expr then Expr_Extract (upper, lower, expr) else e
        | Expr_Concat (l, r) ->
            let nl = self#visit_expr l in
            let nr = self#visit_expr r in
            if nl <> l || nr <> r then Expr_Concat (nl, nr) else e
        | Expr_Literal l -> Expr_Literal l
        | Expr_Forall l -> Expr_Forall l
        | Expr_Exists l -> Expr_Exists l
        | Expr_Old e -> Expr_Old (self#visit_expr e)
        | Expr_FunctionOp (i, param) ->
            let param = mapNoCopy self#visit_expr param in
            Expr_FunctionOp (i, param)
      in
      doVisit vis (vis#vexpr e) next e

    method visit_lvar (e : lVar) = doVisit vis (vis#vlvar e) nochildren e

    method visit_type (x : typeT) : typeT =
      doVisit vis (vis#vtype x) nochildren x
  end

class nopBasilVisitor : basilVisitor =
  object
    method vdecl (_ : decl) = DoChildren
    method vprog (_ : moduleT) = DoChildren
    method vproc (_ : procDef) = DoChildren
    method vblock (_ : block) = DoChildren
    method vstmt (_ : stmt) = DoChildren
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
