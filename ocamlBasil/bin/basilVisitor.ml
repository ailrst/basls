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
  method vprog : program -> program visitAction
  method vproc : (bIdent * procDef) -> (bIdent * procDef) visitAction
  method vblock : block -> block visitAction
  method vstmt : statement -> statement visitAction
  method vjump : jump -> jump visitAction
  method vtype : typeT -> typeT visitAction
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

(** a base class for treeVisitors transforming the AST.
    the method visit_stmts is left abstract for subclasses
    to implement. *)
class virtual basilTreeVisitor (vis : #basilVisitor) =
  object (self)
    method visit_prog (p : program) : program =
      let next _ p =
        match p with Prog decls -> Prog (mapNoCopy self#visit_decl decls)
      in
      doVisit vis (vis#vprog p) next p

    method visit_procdef (p : (bIdent * procDef)) : (bIdent * procDef) =
      let ndef v def =
        let (ident, def) =  def in
        match def with
        | PD (beginning, procname, addrdecl, entryblock, internalBlocks, ending) ->
            let entry = entryblock in
            let bodyBlocks =
              match internalBlocks with
              | BSome (b, bl, e) -> BSome (b, (mapNoCopy self#visit_block bl), e)
              | BNone -> BNone
            in
            (ident , PD (beginning, procname, addrdecl, entry,  bodyBlocks, ending))
      in
      doVisit vis (vis#vproc p) ndef p

    method visit_decl (p : declaration) : declaration =
      let next _ p =
        match p with
        | LetDecl _ -> p
        | MemDecl _ -> p
        | VarDecl _ -> p
        | Procedure (id, inparams, outparams, def) ->
            let (_, ndef) = self#visit_procdef (id, def) in
            Procedure (id, inparams, outparams, ndef)
      in
      doVisit vis (vis#vdecl p) next p

    method visit_block (b : block) : block =
      let next _ b =
        match b with
        | B (bg, label, addr, stmts, j, ed) ->
            B
              (bg, label,
                addr,
                mapNoCopy self#visit_statement stmts,
                self#visit_jump j , ed)
      in
      doVisit vis (vis#vblock b) next b

    method visit_statement (s : statement) : statement =
      doVisit vis (vis#vstmt s) nochildren s

    method visit_jump (j : jump) : jump =
      doVisit vis (vis#vjump j) nochildren j

    method visit_type (x : typeT) : typeT =
      doVisit vis (vis#vtype x) nochildren x
  end

class nopBasilVisitor : basilVisitor =
  object
    method vdecl (_ : declaration) = DoChildren
    method vprog (_ : program) = DoChildren
    method vproc (_ : bIdent * procDef) = DoChildren
    method vblock (_ : block) = DoChildren
    method vstmt (_ : statement) = DoChildren
    method vjump (_ : jump) = DoChildren
    method vtype (_ : typeT) = DoChildren
  end

class forwardBasilvisitor (vis : #basilVisitor) =
  object (self)
    inherit basilTreeVisitor vis
  end

let visit_prog (vis : #basilVisitor) (p : program) =
  (new forwardBasilvisitor vis)#visit_prog p

let visit_block (vis : #basilVisitor) (p : block) =
  (new forwardBasilvisitor vis)#visit_block p
