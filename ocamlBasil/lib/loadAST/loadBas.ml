open BasilIR

let () = Printexc.record_backtrace true

let lexbuf_contents lb =
  let open Lexing in
  let pos = lb.lex_curr_pos in
  let len = lb.lex_buffer_len - lb.lex_curr_pos in
  Bytes.to_string (Bytes.sub lb.lex_buffer pos len)

let pp_lexbuf lb =
  Format.print_string "#<lexbuf:<";
  Format.print_string (lexbuf_contents lb);
  Format.print_string ">>"
