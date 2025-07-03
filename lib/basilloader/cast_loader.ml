open BasilIR

let concrete_ast_of_channel (c : in_channel) : AbsBasilIR.moduleT =
  let lexbuf = Lexing.from_channel c in
  try ParBasilIR.pModuleT LexBasilIR.token lexbuf
  with ParBasilIR.Error ->
    let start_pos = Lexing.lexeme_start_p lexbuf
    and end_pos = Lexing.lexeme_end_p lexbuf in
    raise (BNFC_Util.Parse_error (start_pos, end_pos))

let concrete_ast_of_string (c : string) : AbsBasilIR.moduleT =
  let lexbuf = Lexing.from_string c in
  try ParBasilIR.pModuleT LexBasilIR.token lexbuf
  with ParBasilIR.Error ->
    let start_pos = Lexing.lexeme_start_p lexbuf
    and end_pos = Lexing.lexeme_end_p lexbuf in
    raise (BNFC_Util.Parse_error (start_pos, end_pos))
