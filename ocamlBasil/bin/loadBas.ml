open Loader
open BasilIR

let () = Printexc.record_backtrace true 

let output_graph (s : BasilAST.BasilAST.proc list) =
  let gs = List.map Analysis.graph_of_proc s in
  let f = open_out "beans.dot" in
  List.iter
    (fun (x : Analysis.procedure_rec) -> Analysis.Dot.output_graph f x.graph)
    gs;
  close_out f

let process (s : string) =
  let lexbuf = Lexing.from_string s in
  let prog = ParBasilIR.pProgram LexBasilIR.token lexbuf in
  let procs = BasilAST.BasilASTLoader.transProgram prog in
  let oc = open_out "show" in
  List.map (fun p -> BasilAST.BasilAST.show_proc p) procs
  |> List.iter (fun s -> output_string oc s);
  output_graph procs


let read_file f =
  let ic = open_in f in
  let res = ref "" in
  let rec read (c : in_channel) : string =
    try
      res := !res ^ input_line c ^ "\n";
      read c
    with End_of_file -> !res
  in
  read ic


let () = 
  let f = Array.get Sys.argv 1 in
  let i = read_file f in
  process i 


