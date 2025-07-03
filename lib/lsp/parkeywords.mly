
%{
open Lexing

%}


%token TOK_EOF
%token <(int * int) * string> TOK_COMMENT
%token <(int * int) * string> TOK_KEYWORD

%start kwl

%type <Kwtypes.parsed> kwitem
%type <Kwtypes.parsed list> kwl

%%

kwitem : 
  TOK_COMMENT  { Comment ($1) }
  | TOK_KEYWORD { Keyword ($1)  }
    ;

kwl : TOK_EOF { [] } 
  | kwitem kwl { $1 :: $2 }
  ;
