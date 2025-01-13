open BasilAST
open BasilASTVisitor
open BasilAST
open Containers
open Containers
module IntMap = Map.Make (Int)
module StringMap = Map.Make (String)

module Vert = struct
  type t = int [@@deriving show { with_path = false }, eq, ord]

  let hash v = Int.hash v
end

module Edge = struct
  type block_edge = { label : string; stmts : statement list }
  [@@deriving eq]

  let show_block_edge e =
    Printf.sprintf "%s:\n%s" e.label
      (List.map show_statement e.stmts
      |> List.map (fun e -> "  " ^ e)
      |> String.concat "\n")

  let pp_block_edge fmt e = Format.pp_print_string fmt (show_block_edge e)

  let compare_block_edge a b =
    match (a, b) with
    | { label = s1; _ }, { label = s2; _ } -> String.compare s1 s2

  type t = Block of block_edge | Return of expr list | GoTo | Nop
  [@@deriving show { with_path = false }, eq, ord]

  let create_block ~(label : string) (stmts : statement list) =
    Block { label; stmts }

  let default = Nop
end

module G =
  Graph.Imperative.Digraph.ConcreteBidirectionalLabeled (Vert) (Edge)

type procedure_rec = {
  entry : int option;
  graph : G.t;
  return_vertex : int;
  unreachable_vertex : int;
}

let block_edge_with_begin graph begin_block =
  let open Option in
  let* end_v =
    G.succ graph begin_block |> function
    | h :: [] -> Some h
    | [] -> None
    | xs -> None
  in
  let label = G.find_edge graph begin_block end_v |> G.E.label in
  match label with Block _ as b -> Some (begin_block, end_v, b) | _ -> None

let block_with_begin graph begin_block =
  block_edge_with_begin graph begin_block |> Option.map (fun (_, _, b) -> b)

let block_edge_with_end graph end_block =
  let open Option in
  let* begin_block =
    G.pred graph end_block |> function
    | h :: [] -> Some h
    | [] -> None
    | xs -> None
  in
  let edge = G.find_edge graph begin_block end_block |> G.E.label in
  match edge with
  | Block _ as b -> Some (begin_block, end_block, b)
  | _ -> None

let block_with_end graph end_block =
  block_edge_with_end graph end_block |> Option.map (fun (_, _, b) -> b)

let graph_of_proc (p : proc) =
  let blocks =
    List.map (fun (p : block) -> (p.label, p)) p.internal_blocks
  in
  let blocks = StringMap.of_list blocks in

  let g = G.create ~size:(StringMap.cardinal blocks) () in
  let return_vertex = fresh#get () in
  let unreachable_vertex = fresh#get () in
  G.add_vertex g return_vertex;
  G.add_vertex g unreachable_vertex;

  Option.iter (fun p -> print_endline p) p.entry;
  let entry =
    Option.map (fun b -> (StringMap.find b blocks).begin_loc) p.entry
  in

  let add_block b =
    match b with
    | { begin_loc; end_loc; label; stmts; jump; _ } -> (
        G.add_vertex g begin_loc;
        G.add_vertex g end_loc;
        let mainedge =
          G.E.create begin_loc (Edge.create_block ~label stmts) end_loc
        in
        G.add_edge_e g mainedge;
        match jump with
        | GoTo labels ->
            let targets =
              List.map
                (fun l -> StringMap.find l blocks |> fun l -> l.begin_loc)
                labels
            in
            let edges =
              List.map (fun t -> G.E.create end_loc Edge.GoTo t) targets
            in
            List.iter (G.add_edge_e g) edges;
            ()
        | Unreachable -> G.add_edge g end_loc unreachable_vertex
        | Return x ->
            G.add_edge_e g (G.E.create end_loc (Edge.Return x) return_vertex)
        )
  in
  StringMap.iter (fun lab b -> add_block b) blocks;
  { entry; return_vertex; unreachable_vertex; graph = g }

module GG =
  Graph.Persistent.Digraph.ConcreteBidirectionalLabeled (Vert) (Edge)

module Dot = Graph.Graphviz.Dot (struct
  include G

  let safe_label s =
    "\\l"
    ^ (String.to_seq s
      |> Seq.map (function
           | '\n' -> "\\l"
           | '"' -> "\\\""
           | c -> String.make 1 c)
      |> List.of_seq |> String.concat "")
    ^ "\\l"

  let edge_attributes (e : E.t) =
    [ `Label (safe_label @@ Edge.show (E.label e)); `Fontname "Mono" ]

  let default_edge_attributes _ = []
  let get_subgraph _ = None
  let vertex_attributes _ = [ `Shape `Box ]
  let vertex_name v = string_of_int v
  let default_vertex_attributes _ = []
  let graph_attributes _ = []
end)

let output_dot fname p =
  let f = open_out fname in
  Dot.output_graph f p.graph;
  close_out f
