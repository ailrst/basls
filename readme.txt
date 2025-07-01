
A simple proof of concept language server for Basil IR supporting goto definition and the symbol list for 
block and procedure labels

- AST and parser are generated from bnfc [1] (using the ocaml-menhir backend)
- Language server interface uses c-cube/linol [2] and is just based 
  on the example program with some more method stubs filled in

Testing:

  dune build
  dune install

Neovim (astonvim astrolsp.lua) lsp config :

`.il` files are recognised as `skill` language files. 

    ...
    servers = {
       "basillsp"
    },
    config = {
      basillsp = { cmd={"basilLSP"}, filetypes={"skill"}, root_dir = require("lspconfig.util").root_pattern("."),},
    },
    ...

---

1: https://github.com/BNFC/bnfc
2: https://github.com/c-cube/linol
