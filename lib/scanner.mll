{
  (* OCaml declaration*)   
  open Parser
  open Location

  exception Lexing_error of Location.lexeme_pos * string

  let create_hashtable size init =
    let tbl = Hashtbl.create size in
    List.iter (fun (key, data) -> Hashtbl.add tbl key data) init;
    tbl

  let keyword_table =
    create_hashtable 18 [
      ("var", VAR);
      ("if", IF);
      ("return", RETURN);
      ("else", ELSE);
      ("while", WHILE);
      ("do", DO);
      ("int", KW_INT);
      ("char", KW_CHAR);
      ("void", KW_VOID);
      ("bool", KW_BOOL);
      ("interface", INTERFACE);
      ("uses", USES);
      ("provides", PROVIDES);
      ("component", COMPONENT);
      ("connect", CONNECT);
      ("def", DEF);
      ("for", FOR);
      ("true", BOOL(true));
      ("false", BOOL(false));
    ]

  let special_char_table =
    create_hashtable 7 [
      ("\'", '\'');
      ("b", '\b');
      ("f", '\x0C');
      ("t", '\t');
      ("\\", '\\');
      ("r", '\r');
      ("n", '\n');
    ]

  let max_identifier_length = 64
  let max_integer_value = 2147483647
}

(* Declaration of regular expressions *)
let character = [^ '\\']
let digit = ['0'-'9']
let identifier = ['_' 'a'-'z' 'A'-'Z'] ['_' 'a'-'z' 'A'-'Z' '0'-'9']*
let integer_dec = digit+
let integer_hex = "0x" (digit | ['A'-'F'])+
let single_comment = "//"
let multi_comment_open = "/*"
let multi_comment_close = "*/"

(* Declaration of scanner functions *)
rule next_token = parse
  | (' ' | '\t')*
    { next_token lexbuf }
  | '\n'
    { Lexing.new_line lexbuf; next_token lexbuf }

  | identifier as w
    { if String.length w <= 64 then
        try Hashtbl.find keyword_table w
        with Not_found -> ID(w)
      else
        raise
        (
          Lexing_error
          (
            (to_lexeme_position lexbuf),
            (Printf.sprintf "Syntax Error: too long identifier %s (max length = %d characters)" (w) (max_identifier_length))
          )
        )
    }
  | (integer_dec | integer_hex) as i 
    { 
      let ival = int_of_string i in
        if ival <= max_integer_value then
          INT(ival)
        else
          raise
          (
            Lexing_error
            (
              (to_lexeme_position lexbuf),
              (Printf.sprintf "Syntax Error: integer value %d out of range [-%d ... %d]" (ival) (max_integer_value) (max_integer_value))
            )
          )
    }
  | '\'' '\\' _ '\'' as spec
    { let c = (String.sub spec 2 1) in 
        try CHAR(Hashtbl.find special_char_table c)
        with Not_found -> raise
          (
            Lexing_error
            (
              (to_lexeme_position lexbuf),
              (Printf.sprintf "Syntax Error: \\%s is not a valid special character" (c))
            )
          )
      }
  | '\'' character '\'' as c 
    { CHAR(String.get c 1) }

  | single_comment
    { single_line_comment lexbuf; next_token lexbuf }
  | multi_comment_open
    { multi_line_comment lexbuf; next_token lexbuf }
  | '&'
    { REF }
  | '+'
    { PLUS }
  | '-'
    { MINUS }
  | '*'
    { TIMES }
  | '/'
    { DIV }
  | '%'
    { MOD }
  | "+="
    { ASSIGN_PLUS }
  | "-="
    { ASSIGN_MINUS}
  | "*="
    { ASSIGN_TIMES }
  | "/="
    { ASSIGN_DIV }
  | "%="
    { ASSIGN_MOD }
  | "++"
    { PLUSPLUS }
  | "--"
    { MINUSMINUS }
  | '='
    { ASSIGN }
  | "=="
    { EQ }
  | "!="
    { NEQ }
  | '<'
    { LT }
  | "<="
    { LEQ }
  | '>'
    { GT }
  | ">="
    { GEQ }
  | "&&"
    { AND }
  | "||"
    { OR }
  | "!"
    { NOT }
  | '('
    { LR_BRACKET }
  | ')'
    { RR_BRACKET }
  | '['
    { LS_BRACKET }
  | ']'
    { RS_BRACKET }
  | '{'
    { L_BRACKET }
  | '}'
    { R_BRACKET }
  | '.'
    { DOT }
  | ','
    { COMMA }
  | ':'
    { COLON }
  | ';'
    { SEMICOLON }
  | "<-"
    { ARROW }
  | eof
    { EOF }
  | _ as e 
    { 
      raise
      (
        Lexing_error
        (
          (to_lexeme_position lexbuf),
          (Printf.sprintf "Syntax Error: not valid token %c" (e))
        )
      )
    }

and single_line_comment = parse
  | ('\n' | eof)
    { () }
  | _
    { single_line_comment lexbuf }

and multi_line_comment = parse
  | (multi_comment_close)
      { () }
  | multi_comment_open
      { 
        raise 
        (
          Lexing_error
          (
            (to_lexeme_position lexbuf),
            (Printf.sprintf "Syntax Error: nested comments are not allowed")
          )
        )
      }
  | eof
      { 
        raise 
        (
          Lexing_error
          (
            (to_lexeme_position lexbuf),
            (Printf.sprintf "Syntax Error: multi line comment not closed")
          )
        )
      }
  | _
      { multi_line_comment lexbuf }
    