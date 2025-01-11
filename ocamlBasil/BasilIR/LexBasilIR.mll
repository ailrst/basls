(* File generated by the BNF Converter (bnfc 2.9.5). *)

(* Lexer definition for ocamllex. *)

(* preamble *)
{
open ParBasilIR
open Lexing

let symbol_table = Hashtbl.create 8
let _ = List.iter (fun (kwd, tok) -> Hashtbl.add symbol_table kwd tok)
                  [(";", SYMB1);(",", SYMB2);("=", SYMB3);(":", SYMB4);(":=", SYMB5);("(", SYMB6);(")", SYMB7);("->", SYMB8)]

let resword_table = Hashtbl.create 78
let _ = List.iter (fun (kwd, tok) -> Hashtbl.add resword_table kwd tok)
                  [("let", KW_let);("memory", KW_memory);("var", KW_var);("int", KW_int);("bool", KW_bool);("map", KW_map);("address", KW_address);("le", KW_le);("be", KW_be);("load", KW_load);("store", KW_store);("call", KW_call);("indirect", KW_indirect);("assume", KW_assume);("assert", KW_assert);("goto", KW_goto);("unreachable", KW_unreachable);("return", KW_return);("block", KW_block);("entry_block", KW_entry_block);("blocks", KW_blocks);("name", KW_name);("proc", KW_proc);("boolnot", KW_boolnot);("intneg", KW_intneg);("zero_extend", KW_zero_extend);("sign_extend", KW_sign_extend);("extract", KW_extract);("bvconcat", KW_bvconcat);("true", KW_true);("false", KW_false);("bvnot", KW_bvnot);("bvneg", KW_bvneg);("bvand", KW_bvand);("bvor", KW_bvor);("bvadd", KW_bvadd);("bvmul", KW_bvmul);("bvudiv", KW_bvudiv);("bvurem", KW_bvurem);("bvshl", KW_bvshl);("bvlshr", KW_bvlshr);("bvult", KW_bvult);("bvnand", KW_bvnand);("bvnor", KW_bvnor);("bvxor", KW_bvxor);("bvxnor", KW_bvxnor);("bvcomp", KW_bvcomp);("bvsub", KW_bvsub);("bvsdiv", KW_bvsdiv);("bvsrem", KW_bvsrem);("bvsmod", KW_bvsmod);("bvashr", KW_bvashr);("bvule", KW_bvule);("bvugt", KW_bvugt);("bvuge", KW_bvuge);("bvslt", KW_bvslt);("bvsle", KW_bvsle);("bvsgt", KW_bvsgt);("bvsge", KW_bvsge);("bveq", KW_bveq);("bvneq", KW_bvneq);("intadd", KW_intadd);("intmul", KW_intmul);("intsub", KW_intsub);("intdiv", KW_intdiv);("intmod", KW_intmod);("inteq", KW_inteq);("intneq", KW_intneq);("intlt", KW_intlt);("intle", KW_intle);("intgt", KW_intgt);("intge", KW_intge);("booleq", KW_booleq);("boolneq", KW_boolneq);("booland", KW_booland);("boolor", KW_boolor);("boolimplies", KW_boolimplies);("boolequiv", KW_boolequiv)]

let unescapeInitTail (s:string) : string =
  let rec unesc s = match s with
      '\\'::c::cs when List.mem c ['\"'; '\\'; '\''] -> c :: unesc cs
    | '\\'::'n'::cs  -> '\n' :: unesc cs
    | '\\'::'t'::cs  -> '\t' :: unesc cs
    | '\\'::'r'::cs  -> '\r' :: unesc cs
    | '\"'::[]    -> []
    | '\''::[]    -> []
    | c::cs      -> c :: unesc cs
    | _         -> []
  (* explode/implode from caml FAQ *)
  in let explode (s : string) : char list =
      let rec exp i l =
        if i < 0 then l else exp (i - 1) (s.[i] :: l) in
      exp (String.length s - 1) []
  in let implode (l : char list) : string =
      let res = Buffer.create (List.length l) in
      List.iter (Buffer.add_char res) l;
      Buffer.contents res
  in implode (unesc (List.tl (explode s)))

let incr_lineno (lexbuf:Lexing.lexbuf) : unit =
    let pos = lexbuf.lex_curr_p in
        lexbuf.lex_curr_p <- { pos with
            pos_lnum = pos.pos_lnum + 1;
            pos_bol = pos.pos_cnum;
        }
}

(* BNFC character classes *)
let _letter = ['a'-'z' 'A'-'Z' '\192' - '\255'] # ['\215' '\247']    (*  isolatin1 letter FIXME *)
let _upper  = ['A'-'Z' '\192'-'\221'] # '\215'      (*  capital isolatin1 letter FIXME *)
let _lower  = ['a'-'z' '\222'-'\255'] # '\247'      (*  small isolatin1 letter FIXME *)
let _digit  = ['0'-'9']                             (*  _digit *)
let _idchar = _letter | _digit | ['_' '\'']         (*  identifier character *)
let _universal = _                                  (* universal: any character *)

(* reserved words consisting of special symbols *)
let rsyms = ";" | "," | "=" | ":" | ":=" | "(" | ")" | "->"

(* user-defined token types *)
let bVTYPE = "bv" _digit +
let bIdent = ('#' | '$' | '_' | '~' | _letter)('#' | '$' | '.' | '_' | '~' | (_digit | _letter)) *
let beginList = '['
let endList = ']'
let beginRec = '{'
let endRec = '}'
let str = '"' ([^ '"' '\\']| '\\' ('"' | '\\' | 'f' | 'n' | 'r' | 't')) * '"'
let integerHex = "0x" ('a' | 'b' | 'c' | 'd' | 'e' | 'f' | _digit)+
let bitvectorHex = "0x" ('a' | 'b' | 'c' | 'd' | 'e' | 'f' | _digit)+

(* lexing rules *)
rule token =
  parse "//" (_ # '\n')*
                { token lexbuf }
      | "/*" [^ '*']* '*' ([^ '*' '/'][^ '*']* '*' | '*')* '/'
                { token lexbuf }
      | rsyms   { let x = lexeme lexbuf in try Hashtbl.find symbol_table x with Not_found -> failwith ("internal lexer error: reserved symbol " ^ x ^ " not found in hashtable") }
      | bVTYPE  { let l = lexeme lexbuf in try Hashtbl.find resword_table l with Not_found -> TOK_BVTYPE l }
      | bIdent  { let l = lexeme lexbuf in try Hashtbl.find resword_table l with Not_found -> TOK_BIdent ((lexeme_start lexbuf, lexeme_end lexbuf), l) }
      | beginList
                { let l = lexeme lexbuf in try Hashtbl.find resword_table l with Not_found -> TOK_BeginList ((lexeme_start lexbuf, lexeme_end lexbuf), l) }
      | endList { let l = lexeme lexbuf in try Hashtbl.find resword_table l with Not_found -> TOK_EndList ((lexeme_start lexbuf, lexeme_end lexbuf), l) }
      | beginRec
                { let l = lexeme lexbuf in try Hashtbl.find resword_table l with Not_found -> TOK_BeginRec ((lexeme_start lexbuf, lexeme_end lexbuf), l) }
      | endRec  { let l = lexeme lexbuf in try Hashtbl.find resword_table l with Not_found -> TOK_EndRec ((lexeme_start lexbuf, lexeme_end lexbuf), l) }
      | str     { let l = lexeme lexbuf in try Hashtbl.find resword_table l with Not_found -> TOK_Str l }
      | integerHex
                { let l = lexeme lexbuf in try Hashtbl.find resword_table l with Not_found -> TOK_IntegerHex l }
      | bitvectorHex
                { let l = lexeme lexbuf in try Hashtbl.find resword_table l with Not_found -> TOK_BitvectorHex l }
      | _letter _idchar*
                { let l = lexeme lexbuf in try Hashtbl.find resword_table l with Not_found -> TOK_Ident l }
      | _digit+ { TOK_Integer (int_of_string (lexeme lexbuf)) }
      | _digit+ '.' _digit+ ('e' ('-')? _digit+)?
                { TOK_Double (float_of_string (lexeme lexbuf)) }
      | '\"' (([^ '\"' '\\' '\n']) | ('\\' ('\"' | '\\' | '\'' | 'n' | 't' | 'r')))* '\"'
                { TOK_String (unescapeInitTail (lexeme lexbuf)) }
      | '\'' (([^ '\'' '\\']) | ('\\' ('\\' | '\'' | 'n' | 't' | 'r'))) '\''
                { TOK_Char (unescapeInitTail (lexeme lexbuf)).[0] }
      | [' ' '\t' '\r']
                { token lexbuf }
      | '\n'    { incr_lineno lexbuf; token lexbuf }
      | eof     { TOK_EOF }
