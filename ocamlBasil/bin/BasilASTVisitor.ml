(****************************************************************
 * visitor class
 *
 * This code follows the pattern used in the cilVisitor class in
 * George Necula's excellent CIL (https://people.eecs.berkeley.edu/~necula/cil/)
 * and makes use of the generic Visitor module that is copied from CIL.
 ****************************************************************)

open BasilAST.BasilAST
open Visitor

class type basilVisitor = object
  method vblock : block -> block visitAction
  method vstmt : statement -> statement visitAction
  method vjump : jump -> jump visitAction
  method vtype : btype -> btype visitAction
  method vlvar : lVar -> lVar visitAction
  method vexpr : expr -> expr visitAction
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
    method visit_block (b : block) : block =
      let next _ b =
        match b with
        | { label; stmts; jump; _ } ->
            let stmts = mapNoCopy self#visit_statement stmts in
            let jump = self#visit_jump jump in
            if stmts <> b.stmts || jump <> b.jump then { b with stmts; jump }
            else b
      in
      doVisit vis (vis#vblock b) next b

    method visit_statement (s : statement) : statement =
      let next _ b =
        match b with
        | Assign (o, expr) -> Assign (self#visit_lvar o, self#visit_expr expr)
        | Load (lVar, endian, memory, addr, size) ->
            let nlv = self#visit_lvar lVar in
            let nadr = self#visit_expr addr in
            if nlv <> lVar || nadr <> addr then
              Load (nlv, endian, memory, nadr, size)
            else b
        | Store (endian, bIdent, addr, value, size) ->
            let nadr = self#visit_expr addr in
            let nvalue = self#visit_expr value in
            if nadr <> addr || nvalue <> value then
              Store (endian, bIdent, nadr, nvalue, size)
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
        match expr_view e with
        | RVar (bIdent, typeT) -> e
        | BinaryExpr (binOp, l, r) ->
            let nl = self#visit_expr l in
            let nr = self#visit_expr r in
            if nl <> l || nr <> r then binexp ~op:binOp nl nr else e
        | UnaryExpr (unOp, l) ->
            let nl = self#visit_expr l in
            if nl <> l then unexp ~op:unOp l else e
        | ZeroExtend (intVal, expr) ->
            let nl = self#visit_expr expr in
            if nl <> expr then zero_extend ~n_prefix_bits:intVal expr else e
        | SignExtend (intVal, expr) ->
            let nl = self#visit_expr expr in
            if nl <> expr then sign_extend ~n_prefix_bits:intVal expr else e
        | Extract (upper, lower, expr) ->
            let nl = self#visit_expr expr in
            if nl <> expr then bvextract ~hi_incl:upper ~lo_excl:lower expr
            else e
        | Concat (l, r) ->
            let nl = self#visit_expr l in
            let nr = self#visit_expr r in
            if nl <> l || nr <> r then bvconcat nl nr else e
        | BVConst (intVal, bVType) -> e
        | IntConst intVal -> e
        | BoolConst true -> e
        | BoolConst false -> e
      in
      doVisit vis (vis#vexpr e) next e

    method visit_lvar (e : lVar) = doVisit vis (vis#vlvar e) nochildren e

    method visit_type (x : btype) : btype =
      doVisit vis (vis#vtype x) nochildren x
  end

class nopBasilVisitor : basilVisitor =
  object
    method vblock (_ : block) = DoChildren
    method vstmt (_ : statement) = DoChildren
    method vjump (_ : jump) = DoChildren
    method vtype (_ : btype) = DoChildren
    method vexpr (_ : expr) = DoChildren
    method vlvar (_ : lVar) = DoChildren
  end

class forwardBasilvisitor (vis : #basilVisitor) =
  object (self)
    inherit basilTreeVisitor vis
  end

let visit_block (vis : #basilVisitor) (p : block) =
  (new forwardBasilvisitor vis)#visit_block p

let visit_stmt (vis : #basilVisitor) (p : statement) =
  (new forwardBasilvisitor vis)#visit_statement p

let visit_expr (vis : #basilVisitor) (p : expr) =
  (new forwardBasilvisitor vis)#visit_expr p
