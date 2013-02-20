type token =
  | EOF
  | INT of (Range.t * int32)
  | IDENT of (Range.t * string)
  | SEMI of (Range.t)
  | COMMA of (Range.t)
  | LBRACE of (Range.t)
  | RBRACE of (Range.t)
  | IF of (Range.t)
  | ELSE of (Range.t)
  | WHILE of (Range.t)
  | FOR of (Range.t)
  | RETURN of (Range.t)
  | TINT of (Range.t)
  | PLUS of (Range.t)
  | DASH of (Range.t)
  | STAR of (Range.t)
  | SLASH of (Range.t)
  | PERCENT of (Range.t)
  | GT of (Range.t)
  | GTEQ of (Range.t)
  | LT of (Range.t)
  | LTEQ of (Range.t)
  | EQEQ of (Range.t)
  | EQ of (Range.t)
  | BANG of (Range.t)
  | BANGEQ of (Range.t)
  | BAR of (Range.t)
  | AMPER of (Range.t)
  | LPAREN of (Range.t)
  | RPAREN of (Range.t)
  | TILDE of (Range.t)
  | LTLT of (Range.t)
  | GTGT of (Range.t)
  | GTGTGT of (Range.t)

open Parsing;;
# 2 "parser.mly"
open Ast;;
# 41 "parser.ml"
let yytransl_const = [|
    0 (* EOF *);
    0|]

let yytransl_block = [|
  257 (* INT *);
  258 (* IDENT *);
  259 (* SEMI *);
  260 (* COMMA *);
  261 (* LBRACE *);
  262 (* RBRACE *);
  263 (* IF *);
  264 (* ELSE *);
  265 (* WHILE *);
  266 (* FOR *);
  267 (* RETURN *);
  268 (* TINT *);
  269 (* PLUS *);
  270 (* DASH *);
  271 (* STAR *);
  272 (* SLASH *);
  273 (* PERCENT *);
  274 (* GT *);
  275 (* GTEQ *);
  276 (* LT *);
  277 (* LTEQ *);
  278 (* EQEQ *);
  279 (* EQ *);
  280 (* BANG *);
  281 (* BANGEQ *);
  282 (* BAR *);
  283 (* AMPER *);
  284 (* LPAREN *);
  285 (* RPAREN *);
  286 (* TILDE *);
  287 (* LTLT *);
  288 (* GTGT *);
  289 (* GTGTGT *);
    0|]

let yylhs = "\255\255\
\001\000\006\000\003\000\007\000\007\000\009\000\004\000\010\000\
\010\000\011\000\011\000\012\000\008\000\008\000\013\000\013\000\
\014\000\014\000\002\000\015\000\015\000\016\000\016\000\017\000\
\017\000\017\000\018\000\018\000\018\000\018\000\018\000\019\000\
\019\000\019\000\019\000\020\000\020\000\020\000\021\000\021\000\
\022\000\022\000\022\000\022\000\023\000\023\000\023\000\005\000\
\005\000\024\000\024\000\025\000\025\000\026\000\026\000\027\000\
\027\000\027\000\027\000\000\000"

let yylen = "\002\000\
\002\000\004\000\002\000\003\000\000\000\004\000\001\000\000\000\
\001\000\001\000\003\000\001\000\002\000\000\000\000\000\001\000\
\000\000\001\000\001\000\003\000\001\000\003\000\001\000\003\000\
\003\000\001\000\003\000\003\000\003\000\003\000\001\000\003\000\
\003\000\003\000\001\000\003\000\003\000\001\000\003\000\001\000\
\002\000\002\000\002\000\001\000\001\000\003\000\001\000\001\000\
\001\000\005\000\007\000\007\000\001\000\005\000\009\000\004\000\
\003\000\005\000\009\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\007\000\060\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\001\000\012\000\000\000\000\000\000\000\
\000\000\000\000\003\000\000\000\048\000\049\000\053\000\000\000\
\045\000\047\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\040\000\044\000\
\000\000\000\000\000\000\000\000\000\000\013\000\000\000\004\000\
\041\000\042\000\000\000\043\000\002\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\006\000\057\000\000\000\000\000\000\000\
\000\000\009\000\000\000\046\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\039\000\000\000\000\000\000\000\000\000\056\000\000\000\
\000\000\000\000\000\000\050\000\058\000\011\000\018\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\051\000\052\000\016\000\000\000\000\000\000\000\000\000\000\000\
\000\000\054\000\000\000\059\000\000\000\000\000\000\000\000\000\
\055\000"

let yydgoto = "\002\000\
\004\000\103\000\005\000\006\000\018\000\007\000\008\000\019\000\
\009\000\073\000\074\000\020\000\116\000\104\000\032\000\033\000\
\034\000\035\000\036\000\037\000\038\000\039\000\040\000\021\000\
\022\000\100\000\023\000"

let yysindex = "\011\000\
\013\255\000\000\000\000\000\000\018\255\045\255\062\000\080\000\
\035\255\057\255\029\255\000\000\000\000\013\255\042\255\049\255\
\056\255\080\000\000\000\041\255\000\000\000\000\000\000\013\255\
\000\000\000\000\057\255\057\255\057\255\057\255\072\255\060\255\
\067\255\242\254\036\255\084\255\007\255\092\255\000\000\000\000\
\057\255\103\255\057\255\057\255\013\255\000\000\057\255\000\000\
\000\000\000\000\096\255\000\000\000\000\057\255\057\255\057\255\
\057\255\057\255\057\255\057\255\057\255\057\255\057\255\057\255\
\057\255\057\255\057\255\000\000\000\000\097\255\098\255\134\255\
\137\255\000\000\143\255\000\000\067\255\242\254\036\255\036\255\
\084\255\084\255\084\255\084\255\007\255\007\255\007\255\092\255\
\092\255\000\000\086\000\098\000\013\255\057\255\000\000\132\255\
\136\255\138\255\157\255\000\000\000\000\000\000\000\000\155\255\
\057\255\057\255\013\255\080\000\080\000\149\255\151\255\164\255\
\000\000\000\000\000\000\156\255\092\000\104\000\057\255\098\000\
\176\255\000\000\183\255\000\000\092\000\080\000\158\255\104\000\
\000\000"

let yyrindex = "\000\000\
\064\000\000\000\000\000\000\000\000\000\000\000\000\000\004\255\
\000\000\000\000\000\000\000\000\000\000\074\000\000\000\000\000\
\000\000\004\255\000\000\000\000\000\000\000\000\000\000\052\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\024\255\
\010\255\118\255\019\255\210\255\130\255\047\255\000\000\000\000\
\000\000\000\000\000\000\000\000\195\255\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\197\255\
\000\000\000\000\000\000\000\000\230\255\038\000\006\000\026\000\
\222\255\242\255\254\255\018\000\150\255\170\255\190\255\079\255\
\110\255\000\000\000\000\000\000\000\000\201\255\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\195\255\000\000\177\255\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\201\255\000\000\
\000\000\000\000\000\000\000\000\000\000\177\255\000\000\000\000\
\000\000"

let yygindex = "\000\000\
\000\000\246\255\191\000\000\000\154\255\000\000\183\000\200\000\
\212\255\113\000\131\000\000\000\101\000\119\000\000\000\196\000\
\197\000\217\255\030\000\056\000\037\000\231\255\000\000\145\000\
\174\255\144\255\168\255"

let yytablesize = 370
let yytable = "\031\000\
\072\000\049\000\050\000\101\000\052\000\122\000\115\000\056\000\
\099\000\014\000\057\000\001\000\021\000\021\000\014\000\129\000\
\079\000\080\000\051\000\065\000\066\000\026\000\026\000\115\000\
\003\000\114\000\019\000\019\000\010\000\101\000\068\000\124\000\
\070\000\071\000\121\000\021\000\075\000\024\000\021\000\124\000\
\026\000\090\000\114\000\026\000\026\000\026\000\011\000\026\000\
\072\000\038\000\038\000\041\000\019\000\058\000\059\000\060\000\
\061\000\025\000\026\000\038\000\038\000\012\000\072\000\047\000\
\038\000\038\000\038\000\038\000\038\000\043\000\027\000\038\000\
\038\000\038\000\053\000\038\000\044\000\038\000\038\000\038\000\
\028\000\036\000\036\000\045\000\029\000\054\000\030\000\081\000\
\082\000\083\000\084\000\036\000\036\000\055\000\110\000\111\000\
\036\000\036\000\036\000\036\000\036\000\088\000\089\000\036\000\
\036\000\036\000\067\000\036\000\069\000\036\000\036\000\036\000\
\037\000\037\000\062\000\063\000\064\000\085\000\086\000\087\000\
\023\000\023\000\037\000\037\000\076\000\091\000\092\000\037\000\
\037\000\037\000\037\000\037\000\035\000\035\000\037\000\037\000\
\037\000\093\000\037\000\094\000\037\000\037\000\037\000\023\000\
\023\000\095\000\023\000\035\000\035\000\035\000\035\000\035\000\
\032\000\032\000\035\000\035\000\035\000\109\000\035\000\105\000\
\035\000\035\000\035\000\106\000\108\000\107\000\119\000\032\000\
\032\000\032\000\032\000\032\000\034\000\034\000\032\000\032\000\
\032\000\117\000\032\000\118\000\032\000\032\000\032\000\125\000\
\120\000\126\000\128\000\034\000\034\000\034\000\034\000\034\000\
\033\000\033\000\034\000\034\000\034\000\008\000\034\000\010\000\
\034\000\034\000\034\000\017\000\042\000\015\000\048\000\033\000\
\033\000\033\000\033\000\033\000\031\000\031\000\033\000\033\000\
\033\000\046\000\033\000\112\000\033\000\033\000\033\000\102\000\
\029\000\029\000\127\000\031\000\031\000\031\000\031\000\031\000\
\020\000\020\000\031\000\031\000\031\000\123\000\031\000\029\000\
\029\000\029\000\029\000\029\000\030\000\030\000\029\000\029\000\
\029\000\077\000\029\000\078\000\113\000\000\000\000\000\020\000\
\027\000\027\000\020\000\030\000\030\000\030\000\030\000\030\000\
\024\000\024\000\030\000\030\000\030\000\000\000\030\000\027\000\
\027\000\027\000\027\000\027\000\028\000\028\000\027\000\027\000\
\027\000\000\000\027\000\024\000\025\000\025\000\024\000\024\000\
\024\000\000\000\024\000\028\000\028\000\028\000\028\000\028\000\
\022\000\022\000\028\000\028\000\028\000\000\000\028\000\025\000\
\000\000\000\000\025\000\025\000\025\000\005\000\025\000\000\000\
\005\000\005\000\005\000\000\000\005\000\005\000\005\000\022\000\
\022\000\005\000\022\000\000\000\005\000\000\000\005\000\000\000\
\005\000\005\000\005\000\005\000\000\000\000\000\005\000\005\000\
\005\000\013\000\005\000\005\000\014\000\000\000\015\000\013\000\
\016\000\017\000\014\000\000\000\096\000\013\000\097\000\098\000\
\014\000\000\000\096\000\013\000\016\000\017\000\014\000\000\000\
\000\000\013\000\016\000\017\000\014\000\000\000\000\000\000\000\
\097\000\098\000"

let yycheck = "\010\000\
\045\000\027\000\028\000\092\000\030\000\118\000\109\000\022\001\
\091\000\006\001\025\001\001\000\003\001\004\001\011\001\128\000\
\056\000\057\000\029\000\013\001\014\001\003\001\004\001\126\000\
\012\001\108\000\003\001\004\001\011\001\118\000\041\000\120\000\
\043\000\044\000\117\000\026\001\047\000\003\001\029\001\128\000\
\022\001\067\000\125\000\025\001\026\001\027\001\002\001\029\001\
\093\000\003\001\004\001\023\001\029\001\018\001\019\001\020\001\
\021\001\001\001\002\001\013\001\014\001\000\000\107\000\023\001\
\018\001\019\001\020\001\021\001\022\001\028\001\014\001\025\001\
\026\001\027\001\003\001\029\001\028\001\031\001\032\001\033\001\
\024\001\003\001\004\001\028\001\028\001\026\001\030\001\058\000\
\059\000\060\000\061\000\013\001\014\001\027\001\105\000\106\000\
\018\001\019\001\020\001\021\001\022\001\065\000\066\000\025\001\
\026\001\027\001\015\001\029\001\006\001\031\001\032\001\033\001\
\003\001\004\001\031\001\032\001\033\001\062\000\063\000\064\000\
\003\001\004\001\013\001\014\001\029\001\029\001\029\001\018\001\
\019\001\020\001\021\001\022\001\003\001\004\001\025\001\026\001\
\027\001\004\001\029\001\003\001\031\001\032\001\033\001\026\001\
\027\001\003\001\029\001\018\001\019\001\020\001\021\001\022\001\
\003\001\004\001\025\001\026\001\027\001\003\001\029\001\028\001\
\031\001\032\001\033\001\028\001\008\001\028\001\003\001\018\001\
\019\001\020\001\021\001\022\001\003\001\004\001\025\001\026\001\
\027\001\029\001\029\001\029\001\031\001\032\001\033\001\008\001\
\029\001\003\001\029\001\018\001\019\001\020\001\021\001\022\001\
\003\001\004\001\025\001\026\001\027\001\003\001\029\001\003\001\
\031\001\032\001\033\001\003\001\014\000\029\001\024\000\018\001\
\019\001\020\001\021\001\022\001\003\001\004\001\025\001\026\001\
\027\001\018\000\029\001\107\000\031\001\032\001\033\001\093\000\
\003\001\004\001\126\000\018\001\019\001\020\001\021\001\022\001\
\003\001\004\001\025\001\026\001\027\001\119\000\029\001\018\001\
\019\001\020\001\021\001\022\001\003\001\004\001\025\001\026\001\
\027\001\054\000\029\001\055\000\108\000\255\255\255\255\026\001\
\003\001\004\001\029\001\018\001\019\001\020\001\021\001\022\001\
\003\001\004\001\025\001\026\001\027\001\255\255\029\001\018\001\
\019\001\020\001\021\001\022\001\003\001\004\001\025\001\026\001\
\027\001\255\255\029\001\022\001\003\001\004\001\025\001\026\001\
\027\001\255\255\029\001\018\001\019\001\020\001\021\001\022\001\
\003\001\004\001\025\001\026\001\027\001\255\255\029\001\022\001\
\255\255\255\255\025\001\026\001\027\001\002\001\029\001\255\255\
\005\001\006\001\007\001\255\255\009\001\010\001\011\001\026\001\
\027\001\002\001\029\001\255\255\005\001\255\255\007\001\255\255\
\009\001\010\001\011\001\002\001\255\255\255\255\005\001\006\001\
\007\001\002\001\009\001\010\001\005\001\255\255\007\001\002\001\
\009\001\010\001\005\001\255\255\007\001\002\001\009\001\010\001\
\005\001\255\255\007\001\002\001\009\001\010\001\005\001\255\255\
\255\255\002\001\009\001\010\001\005\001\255\255\255\255\255\255\
\009\001\010\001"

let yynames_const = "\
  EOF\000\
  "

let yynames_block = "\
  INT\000\
  IDENT\000\
  SEMI\000\
  COMMA\000\
  LBRACE\000\
  RBRACE\000\
  IF\000\
  ELSE\000\
  WHILE\000\
  FOR\000\
  RETURN\000\
  TINT\000\
  PLUS\000\
  DASH\000\
  STAR\000\
  SLASH\000\
  PERCENT\000\
  GT\000\
  GTEQ\000\
  LT\000\
  LTEQ\000\
  EQEQ\000\
  EQ\000\
  BANG\000\
  BANGEQ\000\
  BAR\000\
  AMPER\000\
  LPAREN\000\
  RPAREN\000\
  TILDE\000\
  LTLT\000\
  GTGT\000\
  GTGTGT\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'prog) in
    Obj.repr(
# 51 "parser.mly"
             ( _1 )
# 317 "parser.ml"
               : Ast.prog))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : Ast.block) in
    let _2 = (Parsing.peek_val __caml_parser_env 2 : Range.t) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast.exp) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : Range.t) in
    Obj.repr(
# 55 "parser.mly"
                          ( (_1, _3) )
# 327 "parser.ml"
               : 'prog))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'vdecls) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'stmts) in
    Obj.repr(
# 58 "parser.mly"
                 ( (_1, _2) )
# 335 "parser.ml"
               : Ast.block))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'vdecl) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Range.t) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'vdecls) in
    Obj.repr(
# 61 "parser.mly"
                      ( _1::_3 )
# 344 "parser.ml"
               : 'vdecls))
; (fun __caml_parser_env ->
    Obj.repr(
# 62 "parser.mly"
                ( [] )
# 350 "parser.ml"
               : 'vdecls))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : Ast.typ) in
    let _2 = (Parsing.peek_val __caml_parser_env 2 : Range.t * string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Range.t) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : Ast.exp) in
    Obj.repr(
# 65 "parser.mly"
                      ( {v_ty=_1; v_id=snd(_2); v_init=_4 } )
# 360 "parser.ml"
               : 'vdecl))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Range.t) in
    Obj.repr(
# 68 "parser.mly"
         ( TInt )
# 367 "parser.ml"
               : Ast.typ))
; (fun __caml_parser_env ->
    Obj.repr(
# 72 "parser.mly"
                ( [] )
# 373 "parser.ml"
               : 'vdecllist))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'vdeclplus) in
    Obj.repr(
# 73 "parser.mly"
              ( _1 )
# 380 "parser.ml"
               : 'vdecllist))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'vdecl) in
    Obj.repr(
# 76 "parser.mly"
            ( [_1] )
# 387 "parser.ml"
               : 'vdeclplus))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'vdecl) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Range.t) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'vdeclplus) in
    Obj.repr(
# 77 "parser.mly"
                          ( _1::_3 )
# 396 "parser.ml"
               : 'vdeclplus))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Range.t * string) in
    Obj.repr(
# 80 "parser.mly"
          ( _1 )
# 403 "parser.ml"
               : 'lhs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : Ast.stmt) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'stmts) in
    Obj.repr(
# 83 "parser.mly"
               ( _1::_2 )
# 411 "parser.ml"
               : 'stmts))
; (fun __caml_parser_env ->
    Obj.repr(
# 84 "parser.mly"
                 ( [] )
# 417 "parser.ml"
               : 'stmts))
; (fun __caml_parser_env ->
    Obj.repr(
# 87 "parser.mly"
                 ( None )
# 423 "parser.ml"
               : 'stmtOPT))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast.stmt) in
    Obj.repr(
# 88 "parser.mly"
                 ( Some _1 )
# 430 "parser.ml"
               : 'stmtOPT))
; (fun __caml_parser_env ->
    Obj.repr(
# 91 "parser.mly"
                 ( None )
# 436 "parser.ml"
               : 'expOPT))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast.exp) in
    Obj.repr(
# 92 "parser.mly"
                 ( Some _1 )
# 443 "parser.ml"
               : 'expOPT))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'E4) in
    Obj.repr(
# 95 "parser.mly"
       ( _1 )
# 450 "parser.ml"
               : Ast.exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'E4) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Range.t) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'E5) in
    Obj.repr(
# 98 "parser.mly"
              ( Binop (Or, _1, _3) )
# 459 "parser.ml"
               : 'E4))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'E5) in
    Obj.repr(
# 99 "parser.mly"
       ( _1 )
# 466 "parser.ml"
               : 'E4))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'E5) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Range.t) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'E6) in
    Obj.repr(
# 102 "parser.mly"
                ( Binop (And, _1, _3) )
# 475 "parser.ml"
               : 'E5))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'E6) in
    Obj.repr(
# 103 "parser.mly"
       ( _1 )
# 482 "parser.ml"
               : 'E5))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'E6) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Range.t) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'E7) in
    Obj.repr(
# 106 "parser.mly"
               ( Binop (Eq, _1, _3) )
# 491 "parser.ml"
               : 'E6))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'E6) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Range.t) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'E7) in
    Obj.repr(
# 107 "parser.mly"
                 ( Binop (Neq, _1, _3) )
# 500 "parser.ml"
               : 'E6))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'E7) in
    Obj.repr(
# 108 "parser.mly"
       ( _1 )
# 507 "parser.ml"
               : 'E6))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'E7) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Range.t) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'E8) in
    Obj.repr(
# 111 "parser.mly"
             ( Binop (Lt, _1, _3) )
# 516 "parser.ml"
               : 'E7))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'E7) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Range.t) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'E8) in
    Obj.repr(
# 112 "parser.mly"
               ( Binop (Lte, _1, _3) )
# 525 "parser.ml"
               : 'E7))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'E7) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Range.t) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'E8) in
    Obj.repr(
# 113 "parser.mly"
             ( Binop (Gt, _1, _3) )
# 534 "parser.ml"
               : 'E7))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'E7) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Range.t) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'E8) in
    Obj.repr(
# 114 "parser.mly"
               ( Binop (Gte, _1, _3) )
# 543 "parser.ml"
               : 'E7))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'E8) in
    Obj.repr(
# 115 "parser.mly"
       ( _1 )
# 550 "parser.ml"
               : 'E7))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'E8) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Range.t) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'E9) in
    Obj.repr(
# 118 "parser.mly"
               ( Binop (Shl, _1, _3) )
# 559 "parser.ml"
               : 'E8))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'E8) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Range.t) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'E9) in
    Obj.repr(
# 119 "parser.mly"
                 ( Binop (Shr, _1, _3) )
# 568 "parser.ml"
               : 'E8))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'E8) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Range.t) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'E9) in
    Obj.repr(
# 120 "parser.mly"
               ( Binop (Sar, _1, _3) )
# 577 "parser.ml"
               : 'E8))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'E9) in
    Obj.repr(
# 121 "parser.mly"
       ( _1 )
# 584 "parser.ml"
               : 'E8))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'E9) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Range.t) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'E10) in
    Obj.repr(
# 124 "parser.mly"
                ( Binop (Plus, _1, _3) )
# 593 "parser.ml"
               : 'E9))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'E9) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Range.t) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'E10) in
    Obj.repr(
# 125 "parser.mly"
                ( Binop (Minus, _1, _3) )
# 602 "parser.ml"
               : 'E9))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'E10) in
    Obj.repr(
# 126 "parser.mly"
        ( _1 )
# 609 "parser.ml"
               : 'E9))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'E10) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Range.t) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'E11) in
    Obj.repr(
# 129 "parser.mly"
                 ( Binop (Times, _1, _3) )
# 618 "parser.ml"
               : 'E10))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'E11) in
    Obj.repr(
# 130 "parser.mly"
        ( _1 )
# 625 "parser.ml"
               : 'E10))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : Range.t) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'E11) in
    Obj.repr(
# 133 "parser.mly"
             ( Unop (Neg, _2) )
# 633 "parser.ml"
               : 'E11))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : Range.t) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'E11) in
    Obj.repr(
# 134 "parser.mly"
             ( Unop (Lognot, _2) )
# 641 "parser.ml"
               : 'E11))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : Range.t) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'E11) in
    Obj.repr(
# 135 "parser.mly"
              ( Unop (Not, _2) )
# 649 "parser.ml"
               : 'E11))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'E12) in
    Obj.repr(
# 136 "parser.mly"
        ( _1 )
# 656 "parser.ml"
               : 'E11))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Range.t * int32) in
    Obj.repr(
# 139 "parser.mly"
        ( Cint (snd _1) )
# 663 "parser.ml"
               : 'E12))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Range.t) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Ast.exp) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Range.t) in
    Obj.repr(
# 140 "parser.mly"
                      ( _2 )
# 672 "parser.ml"
               : 'E12))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Range.t * string) in
    Obj.repr(
# 141 "parser.mly"
            ( Id (snd _1) )
# 679 "parser.ml"
               : 'E12))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'unmatchedif) in
    Obj.repr(
# 145 "parser.mly"
               (_1)
# 686 "parser.ml"
               : Ast.stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'matchedif) in
    Obj.repr(
# 146 "parser.mly"
             (_1)
# 693 "parser.ml"
               : Ast.stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : Range.t) in
    let _2 = (Parsing.peek_val __caml_parser_env 3 : Range.t) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.exp) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Range.t) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'unmatchedstmt) in
    Obj.repr(
# 149 "parser.mly"
                                      (If(_3,_5,None))
# 704 "parser.ml"
               : 'unmatchedif))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 6 : Range.t) in
    let _2 = (Parsing.peek_val __caml_parser_env 5 : Range.t) in
    let _3 = (Parsing.peek_val __caml_parser_env 4 : Ast.exp) in
    let _4 = (Parsing.peek_val __caml_parser_env 3 : Range.t) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : 'matchedif) in
    let _6 = (Parsing.peek_val __caml_parser_env 1 : Range.t) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : 'unmatchedif) in
    Obj.repr(
# 150 "parser.mly"
                                                   (If(_3,_5,Some _7))
# 717 "parser.ml"
               : 'unmatchedif))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 6 : Range.t) in
    let _2 = (Parsing.peek_val __caml_parser_env 5 : Range.t) in
    let _3 = (Parsing.peek_val __caml_parser_env 4 : Ast.exp) in
    let _4 = (Parsing.peek_val __caml_parser_env 3 : Range.t) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : 'matchedif) in
    let _6 = (Parsing.peek_val __caml_parser_env 1 : Range.t) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : 'matchedif) in
    Obj.repr(
# 153 "parser.mly"
                                                 (If(_3,_5,Some _7))
# 730 "parser.ml"
               : 'matchedif))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'matchedstmt) in
    Obj.repr(
# 154 "parser.mly"
               (_1)
# 737 "parser.ml"
               : 'matchedif))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : Range.t) in
    let _2 = (Parsing.peek_val __caml_parser_env 3 : Range.t) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.exp) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Range.t) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'unmatchedstmt) in
    Obj.repr(
# 157 "parser.mly"
                                         (While(_3,_5))
# 748 "parser.ml"
               : 'unmatchedstmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 8 : Range.t) in
    let _2 = (Parsing.peek_val __caml_parser_env 7 : Range.t) in
    let _3 = (Parsing.peek_val __caml_parser_env 6 : 'vdecllist) in
    let _4 = (Parsing.peek_val __caml_parser_env 5 : Range.t) in
    let _5 = (Parsing.peek_val __caml_parser_env 4 : 'expOPT) in
    let _6 = (Parsing.peek_val __caml_parser_env 3 : Range.t) in
    let _7 = (Parsing.peek_val __caml_parser_env 2 : 'stmtOPT) in
    let _8 = (Parsing.peek_val __caml_parser_env 1 : Range.t) in
    let _9 = (Parsing.peek_val __caml_parser_env 0 : 'unmatchedstmt) in
    Obj.repr(
# 158 "parser.mly"
                                                                      (For(_3,_5,_7,_9))
# 763 "parser.ml"
               : 'unmatchedstmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'lhs) in
    let _2 = (Parsing.peek_val __caml_parser_env 2 : Range.t) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast.exp) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : Range.t) in
    Obj.repr(
# 161 "parser.mly"
                   ( Assign(Var(snd(_1)), _3) )
# 773 "parser.ml"
               : 'matchedstmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Range.t) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Ast.block) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Range.t) in
    Obj.repr(
# 162 "parser.mly"
                       (Block(_2))
# 782 "parser.ml"
               : 'matchedstmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : Range.t) in
    let _2 = (Parsing.peek_val __caml_parser_env 3 : Range.t) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.exp) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Range.t) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'matchedstmt) in
    Obj.repr(
# 163 "parser.mly"
                                       (While(_3,_5))
# 793 "parser.ml"
               : 'matchedstmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 8 : Range.t) in
    let _2 = (Parsing.peek_val __caml_parser_env 7 : Range.t) in
    let _3 = (Parsing.peek_val __caml_parser_env 6 : 'vdecllist) in
    let _4 = (Parsing.peek_val __caml_parser_env 5 : Range.t) in
    let _5 = (Parsing.peek_val __caml_parser_env 4 : 'expOPT) in
    let _6 = (Parsing.peek_val __caml_parser_env 3 : Range.t) in
    let _7 = (Parsing.peek_val __caml_parser_env 2 : 'stmtOPT) in
    let _8 = (Parsing.peek_val __caml_parser_env 1 : Range.t) in
    let _9 = (Parsing.peek_val __caml_parser_env 0 : 'matchedstmt) in
    Obj.repr(
# 164 "parser.mly"
                                                                    (For(_3,_5,_7,_9))
# 808 "parser.ml"
               : 'matchedstmt))
(* Entry toplevel *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let toplevel (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : Ast.prog)
