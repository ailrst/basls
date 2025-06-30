
{
open BasilIR.ParBasilIR
open Parkeywords
open Lexing

(* copied from auto-generated lexer *)
let resword_table = Hashtbl.create 81
let _ = List.iter (fun (kwd, tok) -> Hashtbl.add resword_table kwd tok)
                  [("axiom", KW_axiom);("memory", KW_memory);("shared", KW_shared);("var", KW_var);("prog", KW_prog);("entry", KW_entry);("le", KW_le);("be", KW_be);("load", KW_load);("store", KW_store);("call", KW_call);("indirect", KW_indirect);("assume", KW_assume);("guard", KW_guard);("assert", KW_assert);("goto", KW_goto);("unreachable", KW_unreachable);("return", KW_return);("block", KW_block);("proc", KW_proc);("true", KW_true);("false", KW_false);("forall", KW_forall);("exists", KW_exists);("old", KW_old);("boolnot", KW_boolnot);("intneg", KW_intneg);("booltobv1", KW_booltobv1);("zero_extend", KW_zero_extend);("sign_extend", KW_sign_extend);("extract", KW_extract);("bvconcat", KW_bvconcat);("eq", KW_eq);("neq", KW_neq);("bvnot", KW_bvnot);("bvneg", KW_bvneg);("bvand", KW_bvand);("bvor", KW_bvor);("bvadd", KW_bvadd);("bvmul", KW_bvmul);("bvudiv", KW_bvudiv);("bvurem", KW_bvurem);("bvshl", KW_bvshl);("bvlshr", KW_bvlshr);("bvnand", KW_bvnand);("bvnor", KW_bvnor);("bvxor", KW_bvxor);("bvxnor", KW_bvxnor);("bvcomp", KW_bvcomp);("bvsub", KW_bvsub);("bvsdiv", KW_bvsdiv);("bvsrem", KW_bvsrem);("bvsmod", KW_bvsmod);("bvashr", KW_bvashr);("bvule", KW_bvule);("bvugt", KW_bvugt);("bvuge", KW_bvuge);("bvult", KW_bvult);("bvslt", KW_bvslt);("bvsle", KW_bvsle);("bvsgt", KW_bvsgt);("bvsge", KW_bvsge);("intadd", KW_intadd);("intmul", KW_intmul);("intsub", KW_intsub);("intdiv", KW_intdiv);("intmod", KW_intmod);("intlt", KW_intlt);("intle", KW_intle);("intgt", KW_intgt);("intge", KW_intge);("booland", KW_booland);("boolor", KW_boolor);("boolimplies", KW_boolimplies);("require", KW_require);("requires", KW_requires);("ensure", KW_ensure);("ensures", KW_ensures);("invariant", KW_invariant);("rely", KW_rely);("guarantee", KW_guarantee)]

  let incr_lineno (lexbuf:Lexing.lexbuf) : unit =
    let pos = lexbuf.lex_curr_p in
        lexbuf.lex_curr_p <- { pos with
            pos_lnum = pos.pos_lnum + 1;
            pos_bol = pos.pos_cnum;
  }

}

let _letter = ['a'-'z' 'A'-'Z' '\192' - '\255'] # ['\215' '\247']
let keyword = _letter +

rule token =
  parse "//" (_ # '\n')*
                { TOK_COMMENT ((lexeme_start lexbuf, lexeme_end lexbuf), lexeme lexbuf) }
      | "/*" [^ '*']* '*' ([^ '*' '/'][^ '*']* '*' | '*')* '/'
                { TOK_COMMENT ((lexeme_start lexbuf, lexeme_end lexbuf), lexeme lexbuf) }
      | [' ' '\t' '\r'] keyword { let l = lexeme lexbuf in 
            let l = String.sub l 1 ((String.length l) - 1) in
            (Hashtbl.find_opt resword_table l |> (function 
            | None -> token lexbuf
            | Some x -> TOK_KEYWORD ((lexeme_start lexbuf + 1, lexeme_end lexbuf), l))) }
      | [' ' '\t' '\r']
                { token lexbuf }
      | '\n'    { incr_lineno lexbuf; token lexbuf }
      | eof     { TOK_EOF }
      | _ { token lexbuf }
      

