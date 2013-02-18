open Format
let id x = x
let cons x xs = x :: xs
let failwithf fmt = ksprintf failwith fmt
let prerr_endlinef fmt = ksprintf prerr_endline fmt
let ( >:: ) t h = h :: t
let ( >@ )  a b = b @ a


    
let invalid_argf fmt = kprintf invalid_arg fmt
let some x = Some x
let none = None
let memoize f =
  let cache = Hashtbl.create 101 in
  fun v  ->
    try Hashtbl.find cache v
    with | Not_found  -> let r = f v in (Hashtbl.replace cache v r; r)
let finally action f x =
  try let res = f x in action (); res with | e -> (action (); raise e)
let with_dispose ~dispose  f x = finally (fun ()  -> dispose x) f x

(* since ocaml 4.0 *)    
(* external ( |> ) : 'a -> ('a -> 'b) -> 'b = "%revapply" *)
(* external ( & ) : ('a -> 'b) -> 'a -> 'b = "%apply" *)
    
let (|>) a f  = f a
let (&) f a = f a     
external id : 'a -> 'a = "%identity"
external ( !& ) : _ -> unit = "%ignore"
let time f v =
  let start = Unix.gettimeofday () in
  let res = f v in let end_ = Unix.gettimeofday () in (res, (end_ -. start))
let (<|) f x = f x
let (|-) f g x = g (f x)
let (-|) f g x = f (g x)
let flip f x y = f y x
let ( *** )  f g (x,y) = ((f x), (g y))
let (&&&) f g x = ((f x), (g x))
let curry f x y = f (x, y)
let uncurry f (x,y) = f x y
let const x _ = x
let tap f x = f x; x
let is_even x = (x mod 2) == 0
let pp = fprintf
let to_string_of_printer printer v =
  let buf = Buffer.create 30 in
  let () = Format.bprintf buf "@[%a@]" printer v in Buffer.contents buf
let zfold_left ?(start= 0)  ~until  ~acc  f =
  let v = ref acc in
  for x = start to until do v := (f v.contents x) done; v.contents
type 'a cont = 'a -> exn 
let callcc (type u) (f : u cont -> u) =
  let module M = struct exception Return of u end in
    try f (fun x  -> raise (M.Return x)) with | M.Return u -> u
type 'a return =  {
  return: 'b . 'a -> 'b} 
let with_return f =
  let module M = struct exception Return end in
    let r = ref None in
    let return = { return = (fun x  -> r := (Some x); raise M.Return) } in
    try
      let rval = f return in
      match r.contents with
      | None  -> rval
      | Some _ ->
          failwith "with_return exited normally despite return being called"
    with
    | M.Return  ->
        (match r.contents with | None  -> assert false | Some x -> x)
type 'a id = 'a -> 'a 
module Queue =
  struct
    include Queue
    let find t ~f  =
      with_return
        (fun r  -> iter (fun x  -> if f x then r.return (Some x)) t; None)
    let find_map t ~f  =
      with_return
        (fun r  ->
           iter
             (fun x  ->
                match f x with | None  -> () | Some _ as res -> r.return res)
             t;
           None)
    let to_list_rev q = fold (fun acc  v  -> v :: acc) [] q
    let of_list l =
      let q = create () in let _ = List.iter (fun x  -> push x q) l in q
    let rev q = of_list (to_list_rev q)
  end
module List =
  struct
    include List
    let findi p l =
      let rec loop n = function
        | [] -> raise Not_found
        | h :: t ->
            if p n h then (n,h) else loop (n+1) t in
      loop 0 l


    let rev_len l =
      let rec aux l ((n,acc) as r) =
        match l with | [] -> r | x::xs -> aux xs ((n + 1), (x :: acc)) in
      aux l (0, [])
    let hd = function | [] -> failwith "hd" | a::_ -> a
    let tl = function | [] -> failwith "List.tl" | _::l -> l
    let safe_tl = function | [] -> [] | _::l -> l
    let null xs = xs = []
    let rec drop n = function | _::l when n > 0 -> drop (n - 1) l | l -> l
    let lastbut1 ls =
      match ls with
      | [] -> failwith "lastbut1 empty"
      | _ -> let l = List.rev ls in ((List.tl l), (List.hd l))
    let last ls =
      match ls with
      | [] -> failwith "last empty"
      | _ -> List.hd (List.rev ls)
    let split_at n xs =
      let rec aux n acc xs =
        match xs with
        | [] ->
            if n = 0 then (acc, []) else invalid_arg "Index past end of list"
        | h::t as l -> if n = 0 then (acc, l) else aux (n - 1) (h :: acc) t in
      if n < 0
      then invalid_arg "split_at n< 0"
      else (let (a,b) = aux n [] xs in ((rev a), b))
    let rec find_map f =
      function
        | [] -> raise Not_found
        | x::xs -> (match f x with | Some y -> y | None  -> find_map f xs)
    let fold_lefti f acc ls =
      fold_left (fun (i,acc)  x  -> ((i + 1), (f i acc x))) (0, acc) ls
    let rec remove x =
      function
        | (y,_)::l when y = x -> l
        | d::l -> d :: (remove x l)
        | [] -> []
    let iteri f lst =
      let i = ref 0 in
      List.iter (fun x  -> let () = f i.contents x in incr i) lst
    type dir = [ `Left | `Right] 
    let reduce_left f lst =
      match lst with
      | [] -> invalid_arg "reduce_left length zero"
      | x::xs ->
          let rec loop x xs =
            match xs with | [] -> x | y::ys -> loop (f x y) ys in
          loop x xs
    let reduce_left_with ~compose  ~f  lst =
      match lst with
      | [] -> invalid_arg "reduce_left length zero"
      | x::xs ->
          let rec loop x xs =
            match xs with | [] -> x | y::ys -> loop (compose x (f y)) ys in
          loop (f x) xs
    let reduce_right_with ~compose  ~f  lst =
      match lst with
      | [] -> invalid_arg "reduce_right length zero"
      | xs ->
          let rec loop xs =
            match xs with
            | [] -> assert false
            | y::[] -> f y
            | y::ys -> compose (f y) (loop ys) in
          loop xs
    let reduce_right compose = reduce_right_with ~compose ~f:(fun x  -> x)
    let init n f = let open Array in to_list (init n f)
    let concat_map f lst = fold_right (fun x  acc  -> (f x) @ acc) lst []
    let rec filter_map f ls =
      match ls with
      | [] -> []
      | x::xs ->
          (match f x with
          | Some y -> y :: (filter_map f xs)
          | None  -> filter_map f xs)
  end
module type MAP =
  sig
    include Map.S
    val of_list : (key* 'a) list -> 'a t
    val of_hashtbl : (key,'a) Hashtbl.t -> 'a t
    val elements : 'a t -> (key* 'a) list
    val add_list : (key* 'a) list -> 'a t -> 'a t
    val find_default : default:'a -> key -> 'a t -> 'a
  end
module MapMake(S:Map.OrderedType) =
  (struct
     include Map.Make(S)
     let of_list lst =
       List.fold_left (fun acc  (k,v)  -> add k v acc) empty lst
     let add_list lst base =
       List.fold_left (fun acc  (k,v)  -> add k v acc) base lst
     let of_hashtbl tbl =
       Hashtbl.fold (fun k  v  acc  -> add k v acc) tbl empty
     let elements map = fold (fun k  v  acc  -> (k, v) :: acc) map []
     let find_default ~default  k m =
       try find k m with | Not_found  -> default
   end : (MAP with type  key = S.t ))
module type SET =
  sig
    include Set.S
    val of_list : elt list -> t
    val add_list : t -> elt list -> t
    val of_array : elt array -> t
    val add_array : t -> elt array -> t
  end
module SetMake(S:Set.OrderedType) =
  (struct
     include Set.Make(S)
     let of_list = List.fold_left (flip add) empty
     let add_list c = List.fold_left (flip add) c
     let of_array = Array.fold_left (flip add) empty
     let add_array c = Array.fold_left (flip add) c
   end : (SET with type  elt = S.t ))
module SSet = SetMake(String)
module SMap = MapMake(String)
module IMap =
  MapMake(struct type t = int 
                 let compare = Pervasives.compare end)
module ISet =
  SetMake(struct type t = int 
                 let compare = Pervasives.compare end)
let mk_set (type s) ~cmp  =
  let module M =
    struct type t = s 
      let compare = cmp end in
  ((module SetMake( M) : SET with type elt =s)  )
    
let mk_map (type s) ~cmp  =
  let module M =
    struct type t = s 
      let compare = cmp end in
  (module MapMake(M) : MAP with type key =s)
let mk_hashtbl (type s) ~eq  ~hash  =
  let module M = struct type t = s 
                        let equal = eq
                        let hash = hash end in
  (module Hashtbl.Make(M) :  Hashtbl.S with type key = s) 
module Char =
  struct
    include Char
    let is_whitespace =
      function | ' '|'\n'|'\r'|'\t'|'\026'|'\012' -> true | _ -> false
    let is_newline = function | '\n'|'\r' -> true | _ -> false
    let is_digit = function | '0'..'9' -> true | _ -> false
    let is_uppercase c = ('A' <= c) && (c <= 'Z')
    let is_lowercase c = ('a' <= c) && (c <= 'z')
  end
module Return =
  struct
    type 'a t = 'a -> exn 
    let return label v = raise (label v)
    let label (type u) (f : u t -> u) =
      (let module M = struct exception Return of u end in
         try f (fun x  -> M.Return x) with | M.Return u -> u : u )
    let with_label = label
  end
module String =
  struct
    include String
    let init len f =
      let s = create len in
      for i = 0 to len - 1 do unsafe_set s i (f i) done; s
    let is_empty s = s = ""
    let not_empty s = s <> ""
    let starts_with str p =
      let len = length p in
      if (length str) < len
      then false
      else
        Return.label
          (fun label  ->
             for i = 0 to len - 1 do
               if (unsafe_get str i) <> (unsafe_get p i)
               then Return.return label false
               else ()
             done;
             true)
    let ends_with str p =
      let el = length p and sl = length str in
      let diff = sl - el in
      if diff < 0
      then false
      else
        Return.label
          (fun label  ->
             for i = 0 to el - 1 do
               if (get str (diff + i)) <> (get p i)
               then Return.return label false
               else ()
             done;
             true)
    let of_char = make 1
    let drop_while f s =
      let len = length s in
      let found = ref false in
      let i = ref 0 in
      while (i.contents < len) && (not found.contents) do
        if not (f (s.[i.contents])) then found := true else incr i done;
      String.sub s i.contents (len - i.contents)
    let neg n =
      let len = String.length n in
      if (len > 0) && ((n.[0]) = '-')
      then String.sub n 1 (len - 1)
      else "-" ^ n
    let map f s =
      let l = length s in
      if l = 0
      then s
      else
        (let r = create l in
         for i = 0 to l - 1 do unsafe_set r i (f (unsafe_get s i)) done; r)
    let lowercase s = map Char.lowercase s
    let find_from str ofs sub =
      let sublen = length sub in
      if sublen = 0
      then ofs
      else
        (let len = length str in
         if len = 0
         then raise Not_found
         else
           if (0 > ofs) || (ofs >= len)
           then raise (Invalid_argument "index out of bounds")
           else
             Return.label
               (fun label  ->
                  for i = ofs to len - sublen do
                    (let j = ref 0 in
                     while
                       (unsafe_get str (i + j.contents)) =
                         (unsafe_get sub j.contents)
                       do
                       incr j;
                       if j.contents = sublen then Return.return label i done)
                  done;
                  raise Not_found))
    let find str sub = find_from str 0 sub
    let split str sep =
      let p = find str sep in
      let len = length sep in
      let slen = length str in
      ((sub str 0 p), (sub str (p + len) ((slen - p) - len)))
    let rfind_from str suf sub =
      let sublen = length sub and len = length str in
      if sublen = 0
      then len
      else
        if len = 0
        then raise Not_found
        else
          if (0 > suf) || (suf >= len)
          then raise (Invalid_argument "index out of bounds")
          else
            Return.label
              (fun label  ->
                 for i = (suf - sublen) + 1 downto 0 do
                   (let j = ref 0 in
                    while
                      (unsafe_get str (i + j.contents)) =
                        (unsafe_get sub j.contents)
                      do
                      incr j;
                      if j.contents = sublen then Return.return label i done)
                 done;
                 raise Not_found)
    let rfind str sub = rfind_from str ((String.length str) - 1) sub
    let nsplit str sep =
      if str = ""
      then []
      else
        if sep = ""
        then invalid_arg "nsplit: empty sep not allowed"
        else
          (let seplen = String.length sep in
           let rec aux acc ofs =
             if ofs >= 0
             then
               match try Some (rfind_from str ofs sep)
                     with | Not_found  -> None
               with
               | Some idx ->
                   let end_of_sep = (idx + seplen) - 1 in
                   (if end_of_sep = ofs
                    then aux ("" :: acc) (idx - 1)
                    else
                      (let token =
                         sub str (end_of_sep + 1) (ofs - end_of_sep) in
                       aux (token :: acc) (idx - 1)))
               | None  -> (sub str 0 (ofs + 1)) :: acc
             else "" :: acc in
           aux [] ((length str) - 1))
  end
module Ref =
  struct
    let protect r v body =
      let old = r.contents in
      try r := v; (let res = body () in r := old; res)
      with | x -> (r := old; raise x)
    let safe r body =
      let old = r.contents in finally (fun ()  -> r := old) body ()
    let protect2 (r1,v1) (r2,v2) body =
      let o1 = r1.contents and o2 = r2.contents in
      try r1 := v1; r2 := v2; (let res = body () in r1 := o1; r2 := o2; res)
      with | e -> (r1 := o1; r2 := o2; raise e)
    let save2 r1 r2 body =
      let o1 = r1.contents and o2 = r2.contents in
      finally (fun ()  -> r1 := o1; r2 := o2) body ()
    let protects refs vs body =
      let olds = List.map (fun x  -> x.contents) refs in
      try
        List.iter2 (fun ref  v  -> ref := v) refs vs;
        (let res = body () in
         List.iter2 (fun ref  v  -> ref := v) refs olds; res)
      with | e -> (List.iter2 (fun ref  v  -> ref := v) refs olds; raise e)
    let saves (refs : 'a ref list) body =
      let olds = List.map (fun x  -> x.contents) refs in
      finally (fun ()  -> List.iter2 (fun ref  x  -> ref := x) refs olds)
        body ()
    let post r f = let old = r.contents in r := (f old); old
    let pre r f = r := (f r.contents); r.contents
    let swap a b = let buf = a.contents in a := b.contents; b := buf
    let modify x f = x := (f x.contents)
  end
module Option =
  struct
    let may f = function | None  -> () | Some v -> f v
    let map f = function | None  -> None | Some v -> Some (f v)
    let bind f = function | None  -> None | Some v -> f v
    let apply = function | None  -> (fun x  -> x) | Some f -> f
    let filter f = function | Some x when f x -> Some x | _ -> None
    let default v = function | None  -> v | Some v -> v
    let is_some = function | None  -> false | _ -> true
    let is_none = function | None  -> true | _ -> false
    let get_exn s e = match s with | None  -> raise e | Some v -> v
    let get s = get_exn s (Invalid_argument "Option.get")
    let map_default f v = function | None  -> v | Some v2 -> f v2
    let compare ?(cmp= Pervasives.compare)  a b =
      match a with
      | None  -> (match b with | None  -> 0 | Some _ -> (-1))
      | Some x -> (match b with | None  -> 1 | Some y -> cmp x y)
    let eq ?(eq= ( = ))  x y =
      match (x, y) with
      | (None ,None ) -> true
      | (Some a,Some b) -> eq a b
      | _ -> false
  end
module Buffer =
  struct
    include Buffer
    let (+>) buf chr = Buffer.add_char buf chr; buf
    let (+>>) buf str = Buffer.add_string buf str; buf
    let of_channel (ch : in_channel) : Buffer.t =
      (* Buffer.add_channel appears to be broken... *)
      let len = 2048 in
      let str = String.create len in
      let buf = Buffer.create len in
      let nch = ref 1 in
      while !nch <> 0 do
        nch := input ch str 0 len;
        Buffer.add_substring buf str 0 !nch
      done; buf

  end
module Hashtbl =
  struct
    include Hashtbl
    let keys tbl = fold (fun k  _  acc  -> k :: acc) tbl []
    let values tbl = fold (fun _  v  acc  -> v :: acc) tbl []
    let find_default ~default  tbl k =
      try find tbl k with | Not_found  -> default
  end
module Array =
  struct
    include Array
    let fold_left2 f acc a1 a2 =
      let l1 = Array.length a1 and l2 = Array.length a2 in
      if l1 <> l2
      then invalid_arg "Array.fold_left2 length is not equal"
      else
        (let acc = ref acc in
         let rec loop i =
           if i < l1
           then (acc := (f acc.contents (a1.(i)) (a2.(i))); loop (i + 1))
           else acc.contents in
         loop 0)
    let filter_opt t =
      let n = length t in
      let res_size = ref 0 in
      let first_some = ref None in
      for i = 0 to n - 1 do
        (match t.(i) with
         | None  -> ()
         | Some _ as s ->
             (if res_size.contents = 0 then first_some := s else ();
              incr res_size))
      done;
      (match first_some.contents with
       | None  -> [||]
       | Some el ->
           let result = create res_size.contents el in
           let pos = ref 0 in
           let _ =
             for i = 0 to n - 1 do
               match t.(i) with
               | None  -> ()
               | Some x -> (result.(pos.contents) <- x; incr pos)
             done in
           result)
    let filter_map f a = filter_opt (map f a)
    let for_all2 p xs ys =
      let n = length xs in
      let _ =
        if (length ys) <> n then raise (Invalid_argument "Array.for_all2") in
      let rec loop i =
        if i = n
        then true
        else if p (xs.(i)) (ys.(i)) then loop (succ i) else false in
      loop 0
  end
module type STREAM =
  sig
    type 'a t  
    exception Failure
    exception Error of string
    val from : (int -> 'a option) -> 'a t
    val of_list : 'a list -> 'a t
    val of_string : string -> char t
    val of_channel : in_channel -> char t
    val iter : ('a -> unit) -> 'a t -> unit
    val next : 'a t -> 'a
    val empty : 'a t -> unit
    val peek : 'a t -> 'a option
    val junk : 'a t -> unit
    val count : 'a t -> int
    val npeek : int -> 'a t -> 'a list
    val iapp : 'a t -> 'a t -> 'a t
    val icons : 'a -> 'a t -> 'a t
    val ising : 'a -> 'a t
    val lapp : (unit -> 'a t) -> 'a t -> 'a t
    val lcons : (unit -> 'a) -> 'a t -> 'a t
    val lsing : (unit -> 'a) -> 'a t
    val sempty : 'a t
    val slazy : (unit -> 'a t) -> 'a t
    val dump : ('a -> unit) -> 'a t -> unit
    val to_list : 'a t -> 'a list
    val to_string : char t -> string
    val to_string_fmt : ('a -> string,unit,string) format -> 'a t -> string
    val to_string_fun : ('a -> string) -> 'a t -> string
    val of_fun : (unit -> 'a) -> 'a t
    val foldl : ('a -> 'b -> ('a* bool option)) -> 'a -> 'b t -> 'a
    val foldr : ('a -> 'b lazy_t -> 'b) -> 'b -> 'a t -> 'b
    val fold : ('a -> 'a -> ('a* bool option)) -> 'a t -> 'a
    val filter : ('a -> bool) -> 'a t -> 'a t
    val map2 : ('a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t
    val scanl : ('a -> 'b -> 'a) -> 'a -> 'b t -> 'a t
    val scan : ('a -> 'a -> 'a) -> 'a t -> 'a t
    val concat : 'a t t -> 'a t
    val take : int -> 'a t -> 'a t
    val drop : int -> 'a t -> 'a t
    val take_while : ('a -> bool) -> 'a t -> 'a t
    val drop_while : ('a -> bool) -> 'a t -> 'a t
    val comb : ('a t* 'b t) -> ('a* 'b) t
    val split : ('a* 'b) t -> ('a t* 'b t)
    val merge : (bool -> 'a -> bool) -> ('a t* 'a t) -> 'a t
    val switch : ('a -> bool) -> 'a t -> ('a t* 'a t)
    val cons : 'a -> 'a t -> 'a t
    val apnd : 'a t -> 'a t -> 'a t
    val is_empty : 'a t -> bool
    val rev : 'a t -> 'a t
    val tail : 'a t -> 'a t
    val map : ('a -> 'b) -> 'a t -> 'b t
    val dup : 'a t -> 'a t
    val peek_nth : 'a t -> int -> 'a option
    val njunk : int -> 'a t -> unit
  end
module Stream =
  struct
    include Stream
    let rev strm =
      let rec aux (__strm : _ Stream.t) =
        match Stream.peek __strm with
        | Some x ->
            (Stream.junk __strm;
             (let xs = __strm in
              Stream.lapp (fun _  -> aux xs) (Stream.ising x)))
        | _ -> Stream.sempty in
      aux strm
    let tail (__strm : _ Stream.t) =
      match Stream.peek __strm with
      | Some _ -> (Stream.junk __strm; __strm)
      | _ -> Stream.sempty
    let rec map f (__strm : _ Stream.t) =
      match Stream.peek __strm with
      | Some x ->
          (Stream.junk __strm;
           (let xs = __strm in
            Stream.lcons (fun _  -> f x)
              (Stream.slazy (fun _  -> map f xs))))
      | _ -> Stream.sempty
    let peek_nth strm n =
      let rec loop i =
        function
        | x::xs -> if i = 0 then Some x else loop (i - 1) xs
        | [] -> None in
      if n < 0
      then invalid_arg "Stream.peek_nth"
      else loop n (Stream.npeek (n + 1) strm)
    let dup strm = Stream.from (peek_nth strm)
    let njunk n strm = for _i = 1 to n do Stream.junk strm done
    let rec filter f (__strm : _ Stream.t) =
      match Stream.peek __strm with
      | Some x ->
          (Stream.junk __strm;
           (let xs = __strm in
            if f x
            then Stream.icons x (Stream.slazy (fun _  -> filter f xs))
            else Stream.slazy (fun _  -> filter f xs)))
      | _ -> Stream.sempty
  end
module ErrorMonad =
  struct
    type log = string 
    type 'a result =  
      | Left of 'a
      | Right of log 
    let return x = Left x
    let fail x = Right x
    let (>>=) ma f = match ma with | Left v -> f v | Right x -> Right x
    let bind = ( >>= )
    let map f = function | Left v -> Left (f v) | Right s -> Right s
    let (>>|) ma (str,f) =
      match ma with | Left v -> f v | Right x -> Right (x ^ str)
    let (>>?) ma str =
      match ma with | Left _ -> ma | Right x -> Right (x ^ str)
    let (<|>) fa fb a =
      match fa a with | Left _ as x -> x | Right str -> (fb a) >>? str
    let unwrap f a =
      match f a with | Left res -> res | Right msg -> failwith msg
    let mapi_m f xs =
      let rec aux acc xs =
        match xs with
        | [] -> return []
        | x::xs ->
            (f x acc) >>=
              ((fun x  ->
                  (aux (acc + 1) xs) >>= (fun xs  -> return (x :: xs)))) in
      aux 0 xs
  end
module Unix =
  struct
    include Unix
    let folddir ~f  ~init  path =
      let dh = opendir path in
      finally (fun _  -> closedir dh)
        (fun ()  ->
           let rec loop st =
             (try let st' = f st (readdir dh) in fun ()  -> loop st'
              with | End_of_file  -> (fun ()  -> st)) () in
           loop init) ()
    let try_set_close_on_exec fd =
      try set_close_on_exec fd; true with | Invalid_argument _ -> false
    let gen_open_proc_full cmdargs input output error toclose =
      let cmd =
        match cmdargs with
        | x::_ -> x
        | _ -> invalid_arg "Unix.gen_open_proc_full" in
      let cmdargs = Array.of_list cmdargs in
      let cloexec = List.for_all try_set_close_on_exec toclose in
      match fork () with
      | 0 ->
          (dup2 input stdin;
           close input;
           dup2 output stdout;
           close output;
           dup2 error stderr;
           close error;
           if not cloexec then List.iter close toclose else ();
           (try execvp cmd cmdargs with | _ -> exit 127))
      | id -> id
    let open_process_full cmdargs =
      let (in_read,in_write) = pipe () in
      let (out_read,out_write) = pipe () in
      let (err_read,err_write) = pipe () in
      let pid =
        gen_open_proc_full cmdargs out_read in_write err_write
          [in_read; out_write; err_read] in
      close out_read;
      close in_write;
      close err_write;
      (pid, (in_read, out_write, err_read))
    let open_shell_process_full cmd =
      open_process_full ["/bin/sh"; "-c"; cmd]
  end
