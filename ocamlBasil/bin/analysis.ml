open Cfg
open BasilAST
open BasilAST
open BasilASTVisitor
open Util
open Containers
open Containers
module IntMap = Map.Make (Int)
module Bindings = Map.Make (String)
module IdentSet = Set.Make (String)
(* https://link.springer.com/content/pdf/10.1007/978-3-642-37051-9_6.pdf *)

module Env = struct
  type globalState = { globals : btype Bindings.t }
  type localState = (int * btype) Bindings.t

  type bLabel =
    | Empty
    | Filled of statement list * localState
    | Complete of statement list

  type t = { labelling : bLabel IntMap.t }

  class labelling_vis (label : string -> int option) =
    object (this)
      inherit nopBasilVisitor

      method! vexpr e =
        match expr_view e with
        | RVar (bid, t, ind)
          when match label bid with
               | Some x when x <> ind -> true
               | _ -> false ->
            let nid = Option.get_exn_or "unreachable" (label bid) in
            ChangeTo (rvar ~typ:t bid ~index:nid)
        | _ -> DoChildren
    end

  let block_defines (b : Edge.block_edge) (varname : ident) =
    let is l = String.equal (ident_of_lvar l) varname in
    List.exists
      (function
        | Assign (l, _) -> is l
        | DirectCall (ls, _, _) -> List.exists is ls
        | Load (l, _, _, _, _) -> is l
        | _ -> false)
      b.stmts

  type phi = { lvar : lVar; joined : (int * expr) list }

  let mk_phi (l : lVar) (origin_expr : (int * expr) list) =
    let origins, exprs = List.split origin_expr in
    let origins =
      List.map (fun origin -> intconst @@ Z.of_int origin) origins
    in
    let args = origins @ exprs in
    DirectCall ([ l ], "phi", args)

  let of_phi (s : statement) =
    match s with
    | DirectCall ([ l ], "phi", args) ->
        let len = List.length args / 2 in
        assert (len * 2 = List.length args);
        let origins = List.take len args in
        let exprs = List.drop len args in
        let origins =
          List.map
            (fun l ->
              expr_view l |> function
              | IntConst e -> Z.to_int e
              | _ -> failwith "nope")
            origins
        in
        let joined = List.combine origins exprs in
        Some { lvar = l; joined }
    | _ -> None

  let apply_labelling_expr (l : localState) s : statement =
    let v =
      new labelling_vis (fun name ->
          Bindings.find_opt name l |> Option.map fst)
    in
    visit_stmt v s

  let rec apply_lvn p (t : t) begin_block_id (block : Edge.block_edge) : t =
    (* Local value numbering *)
    let open Option in
    IntMap.get_or begin_block_id t.labelling ~default:Empty |> function
    | Filled _ -> t
    | Complete _ -> t
    | Empty ->
        let s = Bindings.empty in
        let add_binding ~variable ~(bindings : localState) ~tag =
          let t = type_of_lvar variable in
          Bindings.add (ident_of_lvar variable) (tag, t) bindings
        in
        let s, statements =
          List.fold_left_map
            (fun a statement ->
              let statement = apply_labelling_expr a statement in
              let a =
                match statement with
                | Assign (l, r) ->
                    add_binding ~variable:l ~bindings:a ~tag:(expr_tag r)
                | Load (l, _, _, _, _) ->
                    add_binding ~variable:l ~bindings:a ~tag:(fresh#get ())
                | DirectCall (lvars, _, _) ->
                    List.fold_left
                      (fun acc variable ->
                        add_binding ~variable ~bindings:acc
                          ~tag:(fresh#get ()))
                      a lvars
                | _ -> a
              in
              (a, statement))
            s block.stmts
        in
        {
          t with
          labelling =
            IntMap.add begin_block_id (Filled (statements, s)) t.labelling;
        }

  and read_variable p t begin_block_id varb =
    let b =
      block_with_begin p.graph begin_block_id |> function
      | Some (Block g) -> Some g
      | _ -> None
    in

    let local =
      match b with
      | Some be ->
          if block_defines be varb then
            let open Option in
            let t = apply_lvn p t begin_block_id be in
            let v =
              let* b = IntMap.get begin_block_id t.labelling in
              let* stmts, s =
                match b with
                | Filled (s, stmts) -> Some (s, stmts)
                | _ -> None
              in
              let* tag, _ = Bindings.find_opt varb s in
              Some tag
            in
            Some (t, Option.get_exn_or "" v)
          else None
      | _ -> None
    in

    match local with
    | Some x -> x
    | None -> read_variable_recursive p t varb begin_block_id

  and read_variable_recursive p s lvar bid =
    let preds = G.pred p.graph bid in
    let variable = ident_of_lvar lvar in
    let x =
      match preds with
      | singlePred :: [] -> (
          block_edge_with_end p.graph singlePred |> function
          | Some (b, e, block) -> read_variable p s b variable
          | None -> read_variable_recursive p s variable singlePred)
      | preds -> 
          let (s, tags) = List.fold_left_map (fun s pred-> read_variable p s pred variable) s preds in
          let tags = List.map (fun x -> intconst (Z.of_int x)) tags in
          let m = List.combine preds tags in
          let phi = mk_phi lvar m in 
      
      in
    x
end
