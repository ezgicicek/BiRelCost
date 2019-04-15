{
open Support.FileInfo
open Support.Error

let lex_error fi s = error_msg Support.Options.Lexer fi "%s" s

let reservedWords = [
  (* Symbols *)
  ("-", fun i -> Parser.DASH i);
  (";", fun i -> Parser.SEMI i);
  ("^", fun i -> Parser.HAT i);
  ("{", fun i -> Parser.LBRACE i);
  ("}", fun i -> Parser.RBRACE i);
  (":", fun i -> Parser.COLON i);
  ("::", fun i -> Parser.DBLCOLON i);
  (",", fun i -> Parser.COMMA i);
  ("<=", fun i -> Parser.LEQ i);
  ("=", fun i -> Parser.EQUAL i);
  ("->", fun i -> Parser.ARROW i);
  ("-->", fun i -> Parser.LARROW i);
  ("=>", fun i -> Parser.DBLARROW i);
  ("+", fun i -> Parser.ADD i);
  ("-", fun i -> Parser.SUB i);
  ("*", fun i -> Parser.MUL i);
  ("X", fun i -> Parser.TIMES i);
  ("/", fun i -> Parser.DIV i);
  ("(", fun i -> Parser.LPAREN i);
  (")", fun i -> Parser.RPAREN i);
  ("[", fun i -> Parser.LBRACK i);
  ("]", fun i -> Parser.RBRACK i);
  ("|", fun i -> Parser.PIPE i);
  ("&", fun i -> Parser.AMP i);
  ("||", fun i -> Parser.OR i);
  ("&&", fun i -> Parser.AND i);
  (".", fun i -> Parser.DOT i);
  
  (* Keywords *)
  ("true", fun i -> Parser.TRUE i);
  ("false", fun i -> Parser.FALSE i);
  ("unit", fun i -> Parser.UNIT i);
  ("unitR", fun i -> Parser.UNITR i);
  ("inf", fun i -> Parser.INF i);
  ("contra", fun i -> Parser.CONTRA i);
  ("fun", fun i -> Parser.FUN i);
  ("case", fun i -> Parser.UNIONCASE i);
  ("caseL", fun i -> Parser.LISTCASE i);
  ("at", fun i -> Parser.AT i);
  ("of", fun i -> Parser.OF i);
  ("inl", fun i -> Parser.INL i);
  ("inr", fun i -> Parser.INR i);
  ("fst", fun i -> Parser.FST i);
  ("snd", fun i -> Parser.SND i);
  ("as", fun i -> Parser.AS i);
  ("as", fun i -> Parser.AS i);
  ("nil", fun i -> Parser.NIL i);
  ("mu", fun i -> Parser.MU i);
  ("let", fun i -> Parser.LET i);
  ("clet", fun i -> Parser.CLET i);
  ("fix", fun i -> Parser.FIX i);
  ("Lam", fun i -> Parser.BIGLAMBDA i);
  ("lam", fun i -> Parser.LAMBDA i);
  ("primitive", fun i -> Parser.PRIMITIVE i);
  ("if", fun i -> Parser.IF i);
  ("then", fun i -> Parser.THEN i);
  ("else", fun i -> Parser.ELSE i);
  ("print", fun i -> Parser.PRINT i);
  ("bool", fun i -> Parser.BOOL i);
  ("boolR", fun i -> Parser.BOOLR i);
  ("num", fun i -> Parser.NUM i);
  ("list", fun i -> Parser.LIST i);
  ("type", fun i -> Parser.TYPE i);
  ("pack", fun i -> Parser.PACK i);
  ("with", fun i -> Parser.WITH i);
  ("size", fun i -> Parser.SIZE i);
  ("cost", fun i -> Parser.COST i);
  ("diff", fun i -> Parser.DIFF i);
  ("max", fun i -> Parser.MAX i);
  ("min", fun i -> Parser.MIN i);
  ("in", fun i -> Parser.IN i);
  ("fl", fun i -> Parser.FLOOR i);
  ("cl", fun i -> Parser.CEIL i);
  ("log", fun i -> Parser.LOG i);
  ("unpack", fun i -> Parser.UNPACK i);
  ("forall", fun i -> Parser.FORALL i);
  ("exists", fun i -> Parser.EXISTS i);
  ("minpowlin", fun i -> Parser.MINPOWLIN i);
  ("minpowcon", fun i -> Parser.MINPOWCONSTANT i);
  ("sum", fun i -> Parser.SUM i);
  ("nat", fun i -> Parser.NAT i);
  ("int", fun i -> Parser.INT i);
  ("intR", fun i -> Parser.INTR i);
  ("U", fun i -> Parser.UNREL i);
  ("Z", fun i -> Parser.ZERO i);
  ("S", fun i -> Parser.SUCC i);
  ("B", fun i -> Parser.BOX i);
]

(* Support functions *)

type buildfun = info -> Parser.token
let (symbolTable : (string,buildfun) Hashtbl.t) = Hashtbl.create 1024
let _ =
  List.iter (fun (str,f) -> Hashtbl.add symbolTable str f) reservedWords

let createID i str =
  try (Hashtbl.find symbolTable str) i
  with _ -> Parser.ID {i=i;v=str}

let lineno   = ref 1
and depth    = ref 0
and start    = ref 0

and filename = ref ""
and startLex = ref dummyinfo

let create inFile stream =
  if not (Filename.is_implicit inFile) then filename := inFile
  else filename := Filename.concat (Sys.getcwd()) inFile;
  lineno := 1; start := 0; Lexing.from_channel stream

let newline lexbuf = incr lineno; start := (Lexing.lexeme_start lexbuf)

let info lexbuf =
  createInfo (!filename) (!lineno) (Lexing.lexeme_start lexbuf - !start)

let text = Lexing.lexeme

let stringBuffer = ref (String.create 2048)
let stringEnd = ref 0

let resetStr () = stringEnd := 0

let addStr ch =
  let x = !stringEnd in
  let buffer = !stringBuffer
in
  if x = String.length buffer then
    begin
      let newBuffer = String.create (x*2) in
      String.blit buffer 0 newBuffer 0 x;
      String.set newBuffer x ch;
      stringBuffer := newBuffer;
      stringEnd := x+1
    end
  else
    begin
      String.set buffer x ch;
      stringEnd := x+1
    end

let getStr () = String.sub (!stringBuffer) 0 (!stringEnd)

let extractLineno yytext offset =
  int_of_string (String.sub yytext offset (String.length yytext - offset))
}


(* The main body of the lexical analyzer *)

rule main = parse
  [' ' '\009' '\012']+     { main lexbuf }

| [' ' '\009' '\012']*("\r")?"\n" { newline lexbuf; main lexbuf }

| "*/" { lex_error (info lexbuf) "Unmatched end of comment" }

| "/*" { depth := 1; startLex := info lexbuf; comment lexbuf; main lexbuf }

| "//" [^ '\n']* { main lexbuf }

| "# " ['0'-'9']+
    { lineno := extractLineno (text lexbuf) 2 - 1; getFile lexbuf }

| "# line " ['0'-'9']+
    { lineno := extractLineno (text lexbuf) 7 - 1; getFile lexbuf }

| ['0'-'9']+
    { Parser.INTV{i=info lexbuf; v=int_of_string (text lexbuf)} }

| ['0'-'9']+ '.' ['0'-'9']+
    { Parser.FLOATV{i=info lexbuf; v=float_of_string (text lexbuf)} }

| ['A'-'Z' 'a'-'z' '_']
  ['A'-'Z' 'a'-'z' '_' '0'-'9' '\'']*
    { createID (info lexbuf) (text lexbuf) }

| ":=" | "<:" | "<-" | "->" | "=>" | "==>" | "<="
| "{|" | "|}" | "<|" | "|>" | "[|" | "|]"
    { createID (info lexbuf) (text lexbuf) }

| ['~' '%' '\\' '+' '-' '&' '|' ':' '`']+
    { createID (info lexbuf) (text lexbuf) }

| ['*' '#' '/' '!' '?' '^' '(' ')' '{' '}' '[' ']' '<' '>' '.' ';' '_' ','
   '=' '\'']
    { createID (info lexbuf) (text lexbuf) }

| "\"" { resetStr(); startLex := info lexbuf; string lexbuf }

| eof { Parser.EOF(info lexbuf) }

| _  { lex_error (info lexbuf) "Illegal character" }

and comment = parse
  "/*"
    { depth := succ !depth; comment lexbuf }
| "*/"
    { depth := pred !depth; if !depth > 0 then comment lexbuf }
| eof
    { lex_error (!startLex) "Comment not terminated" }
| [^ '\n']
    { comment lexbuf }
| "\n"
    { newline lexbuf; comment lexbuf }

and getFile = parse
  " "* "\"" { getName lexbuf }

and getName = parse
  [^ '"' '\n']+ { filename := (text lexbuf); finishName lexbuf }

and finishName = parse
  '"' [^ '\n']* { main lexbuf }

and string = parse
 '\\' { addStr(escaped lexbuf); string lexbuf }
| '\n' { addStr '\n'; newline lexbuf; string lexbuf }
| eof  { lex_error (!startLex) "String not terminated" }
| _    { addStr (Lexing.lexeme_char lexbuf 0); string lexbuf }

and escaped = parse
  'n'	 { '\n' }
| 't'	 { '\t' }
| '\\'	 { '\\' }
| '"'    { '\034'  }
| '\''	 { '\'' }
| ['0'-'9']['0'-'9']['0'-'9']
    {
      let x = int_of_string(text lexbuf) in
      if x > 255 then
	lex_error (info lexbuf) "Illegal character constant"
      else
	Char.chr x
    }
| [^ '"' '\\' 't' 'n' '\'']
    { lex_error (info lexbuf) "Illegal character constant" }

