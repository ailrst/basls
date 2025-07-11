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

  let fresh = new Helper.fresh () in

  let _ = fresh#get () in

  let return_vertex = fresh#get () in
  let unreachable_vertex = fresh#get () in
  G.add_vertex g return_vertex;
  G.add_vertex g unreachable_vertex;

  let add_block (b : block) : int * int =
    match b with
    | { label; stmts; jump; _ } ->
        let begin_vert = fresh#get () in
        let end_vert = fresh#get () in
        G.add_vertex g begin_vert;
        G.add_vertex g end_vert;
        let mainedge =
          G.E.create begin_vert (Edge.create_block ~label stmts) end_vert
        in
        G.add_edge_e g mainedge;
        (begin_vert, end_vert)
  in

  let add_jump verts b =
    match b with
    | { label; stmts; jump; _ } -> (
        let begin_vert, end_vert = StringMap.find label verts in
        match jump with
        | GoTo labels ->
            let targets =
              List.map (fun l -> StringMap.find l verts |> fst) labels
            in
            let edges =
              List.map (fun t -> G.E.create end_vert Edge.GoTo t) targets
            in
            List.iter (G.add_edge_e g) edges;
            ()
        | Unreachable -> G.add_edge g end_vert unreachable_vertex
        | Return x ->
            G.add_edge_e g
              (G.E.create end_vert (Edge.Return x) return_vertex))
  in

  let verts = StringMap.map add_block blocks in

  StringMap.iter (fun i b -> add_jump verts b) blocks;

  let entry = Option.map (fun b -> fst (StringMap.find b verts)) p.entry in

  { entry; return_vertex; unreachable_vertex; graph = g }

module GG =
  Graph.Persistent.Digraph.ConcreteBidirectionalLabeled (Vert) (Edge)

module Dot = Graph.Graphviz.Dot (struct
  include G
  include Graph.Pack

  let addind ind = if ind <= 4  then 4 else 2

  let safe_label s =
    let wrap = 100 in
    let slack = 30 in
    let wrap_p = [ ';'; ')'; '(' ;' ' ] in
    "\\l"
    ^ (String.to_list s
      |> List.fold_left_map
           (fun (l, ind) c ->
             match c with
             | '\n' -> ((0, 0), "\\l")
             | '"' -> ((l, ind), "\\\"")
             | c
               when l >= wrap - slack
                    && List.find_opt (function y -> Char.equal y c) wrap_p
                       |> Option.is_some ->
                 let ind = addind ind in
                 ((0, ind), String.of_char c ^ "\\l" ^ String.make ind ' ' )
             | c when l >= wrap ->
                 let ind = addind ind in
                 ((0, ind), "\\l" ^ String.make ind ' ' ^ String.of_char c)
             | c -> ((l + 1, ind), String.make 1 c))
           (0, 0)
      |> snd |> String.concat "")
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

let viewer_cmd =
  Sys.getenv_opt "GRAPHVIEWER" |> function Some x -> x | None -> "xdg-open"

let viewer_fmt =
  Sys.getenv_opt "GRAPHFORMAT" |> function Some x -> x | None -> "svg"

let display_with_viewer g =
  let tmp = Filename.temp_file "graph" ".dot" in
  let suf = "." ^ viewer_fmt in
  let tmpo = Filename.temp_file "graph-o" suf in
  let oc = open_out tmp in
  output_dot tmp g;
  close_out oc;
  ignore (Sys.command ("dot -Tsvg " ^ tmp ^ " > " ^ tmpo));
  ignore (Sys.command (viewer_cmd ^ " " ^ tmpo));
  Sys.remove tmp
