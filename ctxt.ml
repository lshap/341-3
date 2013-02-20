open LibUtil

(* 
 * One possible implementation of a context is:
 * an association list of the form: (string, uid) list
 *)
type t = (string * Ll.uid) list
exception Scope_error of string 

let dump (c : t) : unit =
failwith "dump not implemented"
      
let empty : t = [] 

(* try to reuse freed, otherwise create new *)
let alloc (sym : string) (c : t) : (t * Ll.uid) =
  let uid = Ll.mk_uid sym in
   c@[(sym, uid)]; (c, uid)
  

let lookup (sym : string) (c : t) : Ll.uid =
  let revlist = List.rev c in
  try
   List.assoc sym revlist
  with
   | Not_found -> raise (Scope_error "variable out of scope")

