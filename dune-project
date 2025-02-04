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
 (name basil_lsp)
 (synopsis "LSP for BASIL IR")
 (depends ocaml dune linol linol-lwt lsp)
 (tags
  (lsp)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
