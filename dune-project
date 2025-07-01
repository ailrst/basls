(lang dune 3.16)

(name basil_lsp)

(generate_opam_files true)

(source
 (github ailrst/basls))

(authors "ailrst")

(maintainers "ailrst")

(license Apache-2.0)

(documentation https://ailrst.github.io/basls)
(using menhir 3.0)


(package
 (name basil_ast)
 (synopsis "LSP for BASIL IR")
 (depends ocaml dune menhir 
          zarith
          ocamlgraph
          hashcons
          containers
          ppx_deriving
          (linol (="0.10")) 
          (linol-lwt (="0.10")) 
          (lsp (>="1.22.0")) 
          )
 (tags (ir)))

(package
 (name basil_lsp)
 (synopsis "LSP for BASIL IR")
 (depends ocaml dune menhir 
          basil_ast
          zarith
          ocamlgraph
          hashcons
          containers
          ppx_deriving
          (linol (="0.10")) 
          (linol-lwt (="0.10")) 
          (lsp (>="1.22.0")) 
          )
 (tags
  (lsp)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
