open LibUtil
open Ast
open Ll

type elt =
 | I of insn 
 | J of terminator
 | L of lbl

type stream = elt list

(* 
 * Parse and AST from a lexbuf 
 * - the filename is used to generate error messages
 *)
let parse (filename : string) (buf : Lexing.lexbuf) : Ast.prog =
  try
    Lexer.reset_lexbuf filename buf;
    Parser.toplevel Lexer.token buf
  with Parsing.Parse_error ->
    failwithf  "Parse error at %s." (Range.string_of_range (Lexer.lex_range buf))

(* 
 * Compile a source binop in to an LL instruction.
 *)
let compile_binop (b : Ast.binop) : Ll.uid -> Ll.operand -> Ll.operand -> Ll.insn  =
  let ib b id op1 op2 = (Ll.Binop (id, b, op1, op2)) in
  let ic c id op1 op2 = (Ll.Icmp (id, c, op1, op2)) in
  match b with
  | Ast.Plus  -> ib Ll.Add
  | Ast.Times -> ib Ll.Mul
  | Ast.Minus -> ib Ll.Sub
  | Ast.And   -> ib Ll.And
  | Ast.Or    -> ib Ll.Or
  | Ast.Shl   -> ib Ll.Shl
  | Ast.Shr   -> ib Ll.Lshr
  | Ast.Sar   -> ib Ll.Ashr

  | Ast.Eq    -> ic Ll.Eq
  | Ast.Neq   -> ic Ll.Ne
  | Ast.Lt    -> ic Ll.Slt
  | Ast.Lte   -> ic Ll.Sle
  | Ast.Gt    -> ic Ll.Sgt
  | Ast.Gte   -> ic Ll.Sge

let compile_unop (u: Ast.unop) : Ll.uid -> Ll.operand -> Ll.insn  =
 let ib b op1 id op2 = (Ll.Binop (id, b, op1, op2)) in
 let ic c op1 id op2 = (Ll.Icmp (id, c, op1, op2)) in
  match u with
    | Ast.Lognot -> ib Ll.Sub (Const (-1l))
    | Ast.Not -> ic Ll.Eq (Const 0l)
    | Ast.Neg ->  ib Ll.Mul (Const (-1l))
 


let rec compile_exp (e: Ast.exp)(c: Ctxt.t)(l:stream): (operand*stream) = 
 begin match e with
  | Cint i -> (Const i, l)
  | Id i -> let newid = gen_sym() in ((Local newid) , [I(Load(newid, Local (Ctxt.lookup i c)))])
  | Ast.Binop (b, e1, e2) -> let newid = gen_sym() in
			     let ce1 = (compile_exp e1 c l) in
			     let ce2 = (compile_exp e2 c l) in
                             let o1 = fst ce1 in
			     let o2 = fst ce2 in
			     let l1 = snd ce1 in
			     let l2 = snd ce2 in
			     let ib = compile_binop b in
			     (Local (newid), (I(ib newid o1 o2))::l2@l1@l)		 
  | Ast.Unop (u, e) -> let newid = gen_sym() in
		       let ce = compile_exp e c l in
                       let o = fst ce in
		       let l1 = snd ce in
		       let iu =  compile_unop u in
		       (Local (newid), (I(iu newid o))::l1@l)
 end

let rec emit_vardecl_stream (v: var_decl list) (c: Ctxt.t): (stream *Ctxt.t) =
  begin match v with
  | h::t ->  let allocation = (Ctxt.alloc h.v_id c) in
             let id =  snd allocation in
	     let c2 = fst allocation in
	     let allocinsn = I (Alloca id) in
	     let l = snd(compile_exp h.v_init c2 [allocinsn]) in
	     let evs = (emit_vardecl_stream t c2) in
	      (fst(evs)@l, snd evs)
  | [] -> ([], c)
 end

let rec emit_stream ((block, ret):Ast.prog) (c: Ctxt.t): (stream) =
  let vdecls = emit_vardecl_stream (fst block) c in []

let compile_prog ((block, ret):Ast.prog) : Ll.prog =
failwith "unimplemented"
