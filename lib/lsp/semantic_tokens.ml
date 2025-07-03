open Tokens
open Common.Util

module SemanticTokensProcessor = struct
  type token_info = { token_type : string; token_modifiers : string list }
  [@@deriving show]

  type t = token_info TokenMap.t

  let lex_tokens_of_string linebreaks s =
    let open Kwtypes in
    let lexbuf = Lexing.from_string s in
    let tp = Parkeywords.kwl Lexkeywords.token lexbuf in
    tp
    |> List.filter_map (function
         | Keyword ((b, e), i) ->
             Some
               ( token_of_char_range linebreaks b e,
                 { token_type = "keyword"; token_modifiers = [] } )
         | _ -> None)
    |> TokenMap.of_list

  let show (x : t) =
    x |> TokenMap.to_list
    |> List.map (fun (k, v) ->
           Printf.sprintf "%s : %s" (Token.show k) (show_token_info v))
    |> String.concat "\n"

  (* dealing with int-indexed tokens *)
  let token_mod = [ "declaration"; "definition" ]

  let token_typ =
    [
      "class";
      "method";
      "function";
      "variable";
      "type";
      "number";
      "parameter";
      "keyword";
    ]

  let to_index m = List.mapi (fun i v -> (v, i)) m |> StringMap.of_list

  let get_token_mod : string -> int =
    let m = to_index token_mod in
    fun i -> StringMap.find i m

  let get_token_typ : string -> int =
    let m = to_index token_typ in
    fun i -> StringMap.find i m

  let semantic_tokens_config =
    let stoken_legend =
      Linol_lwt.SemanticTokensLegend.create ~tokenModifiers:token_mod
        ~tokenTypes:token_typ
    in
    Linol_lwt.SemanticTokensRegistrationOptions.create ~full:(`Bool true)
      ~range:true ~legend:stoken_legend ()

  let token_to_array (tok : Token.t) (tok_info : token_info) =
    (* https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#textDocument_semanticTokens *)
    let { token_type; token_modifiers } = tok_info in
    let line, character = fst tok in
    let length = snd tok in
    let token_modifiers = List.map get_token_mod token_mod in
    let token_type = get_token_typ token_type in
    let modifier_bitset =
      List.map (fun i -> Int.shift_left 1 i) token_modifiers
      |> List.fold_left Int.logor 0
    in
    [| line; character; length; token_type; modifier_bitset |]

  let empty = TokenMap.empty

  let add_one (key : Token.t) ~(token_type : string) ?(token_modifiers = [])
      m =
    TokenMap.add key { token_type; token_modifiers } m

  let add xs (e : 'a -> Token.t * token_info) tm =
    Seq.map e xs |> fun x -> TokenMap.add_seq x tm

  let add_tokmap (xs : 'a TokenMap.t) (e : token_info) tm =
    let ns = TokenMap.map (fun _ -> e) xs in
    TokenMap.union (fun i a b -> Some a) tm ns

  let linecol_relative_to (i : LineCol.t) (j : LineCol.t) =
    let l_i, p_i = i in
    let l_j, p_j = j in
    if l_i = l_j then (0, p_j - p_i) else (l_j - l_i, p_j)

  let token_relative_to (i : Token.t) (j : Token.t) =
    (linecol_relative_to (fst i) (fst j), snd j)

  let to_semantic_tokens_full (tokens : t) =
    (*NOTE: assuming non-overlapping without checking: grammar shouldn't
      allow *)
    let sorted = TokenMap.to_list tokens in
    let relative =
      match sorted with
      | [] -> []
      | hd :: [] -> [ hd ]
      | hd :: tl ->
          let _, nl =
            List.fold_left_map
              (fun ptok (tok, ti) ->
                let nt = token_relative_to ptok tok in
                (tok, (nt, ti)))
              (fst hd) tl
          in
          hd :: nl
    in
    let data =
      List.map (fun (t, i) -> token_to_array t i) relative |> Array.concat
    in
    Linol_lwt.SemanticTokens.create ~data ()
end
