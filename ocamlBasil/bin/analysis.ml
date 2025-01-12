open Cfg
open BasilAST
open BasilAST
open BasilASTVisitor
module IntMap = Map.Make (Int)
module Bindings = Map.Make (String)
module IdentSet = Set.Make (String)
(*
https://link.springer.com/content/pdf/10.1007/978-3-642-37051-9_6.pdf
*)

module Env = struct
  type bLabel = Filled of statement list | Complete of statement list
  type globalState = {
    globals: btype Bindings.t
  }
  type t = { labelling : ((int * btype) Bindings.t) IntMap.t }



  let apply_labelling (t:t) bid (e:expr) = 
    let block = block_with_begin bid in
  ()


end
