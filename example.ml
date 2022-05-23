exception Unimplemented

type empty = |                  (* empty type *)
let absurd (x: empty) = match x with _ -> .

module type CAT = sig
  type ('a,'b) arrow
  val ident  : ('a,'a) arrow
  val compose: ('a,'b) arrow -> ('b,'c) arrow -> ('a,'c) arrow
end

module type PRODUCTS = sig
  include CAT
  val pair:     ('g,'a) arrow -> ('g,'b) arrow -> ('g, 'a * 'b) arrow
  val pi1:      ('a * 'b, 'a) arrow
  val pi2:      ('a * 'b, 'b) arrow
  val ignore:   ('a, unit) arrow
end

module type SUMS = sig
  include CAT
  val case: ('a, 'c) arrow -> ('b, 'c) arrow -> (('a,'b) Either.t, 'c) arrow
  val in1 : ('a, ('a,'b) Either.t) arrow
  val in2 : ('b, ('a,'b) Either.t) arrow
  val absurd: (empty, 'a) arrow
end

module type CCC = sig
  include PRODUCTS
  val lambda: ('g * 'a, 'b) arrow -> ('g, 'a -> 'b) arrow
  val apply : (('a -> 'b) * 'a, 'b) arrow
end

module type BiCCC = sig
  include CCC
  include SUMS with type ('a,'b) arrow := ('a,'b) arrow
  (* NB. the ":=" above prevents having two types named `arrow`. This shadowing
   * would make OCaml sad, even though they'd be the same type. *)
end
                
(* A simple evaluator *)
module Ocaml: BiCCC with type ('a,'b) arrow = 'a -> 'b = struct
  type ('a,'b) arrow = 'a -> 'b
  let ident x = x
  let compose f g x = g (f x)
  let pi1 (x,y) = x let pi2 (x,y) = y let ignore = ignore
  let pair x y env = (x env, y env)
  let lambda f x y = f (x,y) let apply (f,x) = f x
  let in1 x = Either.Left x let in2 y = Either.Right y let absurd = absurd
  let case f g = Either.fold ~left:f ~right:g
end


(* Dynamically checking of arrow types, ugh.
 * This is a lot of ugly boilerplate and the way we're about to use it
 * will probably cause waaaay too many unnecessary runtime checks.
 * But it lets me write the code I want the way I want to write it.
 *)
module Types = struct
  (* type representations *)
  type _ rep =
    | Unit: unit rep | Pair: 'a rep * 'b rep -> ('a * 'b) rep
    | Empty: empty rep | Sum: 'a rep * 'b rep -> (('a,'b) Either.t) rep
    | Fun:  'a rep * 'b rep -> ('a -> 'b) rep

  type tp = Tp: 'a rep -> tp
  exception Types_unequal of tp * tp

  type (_,_) eq = Eq : ('a,'a) eq
  let rec check_equal: type a b. a rep -> b rep -> (a,b) eq = fun a b ->
    match a, b with
    | Unit, Unit -> Eq | Empty, Empty -> Eq
    | Pair (a1,a2), Pair (b1,b2) ->
       (let Eq, Eq = check_equal a1 b1, check_equal a2 b2 in Eq)
    | Fun (a1,a2), Fun (b1,b2) ->
       (let Eq, Eq = check_equal a1 b1, check_equal a2 b2 in Eq)
    | Sum (a1,a2), Sum (b1,b2) ->
       (let Eq, Eq = check_equal a1 b1, check_equal a2 b2 in Eq)
    | Unit, _ | Pair _, _ | Fun _, _ | Empty, _ | Sum _, _
      -> raise (Types_unequal (Tp a, Tp b))

  let check_subtype = check_equal
end

module type BACKEND = sig
  open Types
  type arrow
  val ident: 'a rep -> arrow
  val compose: arrow -> arrow -> arrow
  val pair: arrow -> arrow -> arrow
  val pi1: 'a rep -> 'b rep -> arrow
  val pi2: 'a rep -> 'b rep -> arrow
  val ignore: 'a rep -> arrow
  val lambda: arrow -> arrow
  val apply: 'a rep -> 'b rep -> arrow
  val in1: 'a rep -> 'b rep -> arrow
  val in2: 'a rep -> 'b rep -> arrow
  val case: arrow -> arrow -> arrow
  val absurd: 'a rep -> arrow
end

module Dynamic(C: BiCCC): sig
  open Types
  type arrow = Arrow: 'a rep * 'b rep * ('a,'b) C.arrow -> arrow
  include BACKEND with type arrow := arrow
end
= struct
  open Types
  type arrow = Arrow: 'a rep * 'b rep * ('a,'b) C.arrow -> arrow

  let ident a = Arrow (a, a, C.ident)
  let compose (Arrow (a, b1, f)) (Arrow (b2, c, g): arrow) =
    let Eq = check_subtype b1 b2 in
    Arrow (a, c, C.compose f g)

  let pair (Arrow (cx,a,f)) (Arrow (cx',b,g)) =
    let Eq = check_equal cx cx' in
    Arrow (cx, Pair(a,b), C.pair f g)
  let pi1: type a b. a rep -> b rep -> arrow = fun a b -> Arrow (Pair(a,b), a, C.pi1)
  let pi2: type a b. a rep -> b rep -> arrow = fun a b -> Arrow (Pair(a,b), b, C.pi2)
  let ignore a = Arrow (a, Unit, C.ignore)

  exception NotAPair of tp
  let lambda = function
    | Arrow (Pair(g,a), b, f) -> Arrow (g, (Fun(a,b)), C.lambda f)
    | Arrow (a, _, _) -> raise (NotAPair (Tp a))
  let apply: type a b. a rep -> b rep -> arrow = fun a b ->
    Arrow (Pair(Fun(a,b), a), b, C.apply)

  let absurd a = Arrow (Empty, a, C.absurd)
  let in1: type a b. a rep -> b rep -> arrow = fun a b -> Arrow (a, Sum (a,b), C.in1)
  let in2: type a b. a rep -> b rep -> arrow = fun a b -> Arrow (b, Sum (a,b), C.in2)
  let case (Arrow (a,c,f)) (Arrow (b,c',g)) =
    let Eq = check_equal c c' in
    Arrow (Sum (a,b), c, C.case f g)
end

module Backend = Dynamic(Ocaml)

let x: Backend.arrow = Backend.ignore Types.Unit;;
let r =
  match x with
  | Backend.Arrow (Types.Unit, Types.Unit, f) -> (f (); "yes")
  | _ -> "no"


(* Middle & front end. *)
module Sym: sig
  type t
  val compare: t -> t -> int
  val to_string: t -> string  (* injective *)
  val name: t -> string       (* human-readable *)
  val fresh: string -> t      (* generates a new one each time *)
end = struct
  type t = {name: string; id: int}
  let compare = compare
  let next_id = ref 0
  let fresh name = let x = !next_id in next_id := x + 1; {name = name; id = x}
  let name x = x.name
  let to_string x = Printf.sprintf "%s_%i" x.name x.id
end

module Env = struct
  include Map.Make(Sym)
  (* Prefers later bindings to earlier ones. *)
  let from_list l = List.fold_left (fun cx (k,v) -> add k v cx) empty l
  let add_list l cx = union (fun _k x _y -> Some x) (from_list l) cx
  let add_opt k vopt cx = match vopt with None -> cx | Some v -> add k v cx
end

module type MIDDLE = sig
  type tp
  type term
  val var: tp -> Sym.t -> term
  val letIn: tp -> tp -> Sym.t -> term -> term -> term
  val lam: tp -> tp -> Sym.t -> term -> term
  val app: tp -> tp -> term -> term -> term
  val tuple: (tp * term) list -> term
  val proj: tp list -> int -> term -> term
  (* val letTuple: (tp * Sym.t) list -> tp -> term -> term -> term *)
end

(* module type CONTEXT = sig
 *   include CAT
 *   type 'a cx
 *   val empty: 'a cx
 *   val extend: Sym.t * 'a -> 'a cx -> 'a cx * arrow
 *   val get: 
 * end *)

(* module Cx(C: PRODUCTS) = struct
 *   type 'a cx = (sym * 'a) list
 *   let empty: 'a cx = []
 *   let extend (c: 'a cx) 
 * end *)

module Middle(X: BACKEND): sig
  include MIDDLE 
end = struct
  type tp = Types.tp
  type cx = (??)
  type term = cx -> X.term
end

module type FRONTEND = sig
  type tp
  type term
  (* synthesizing terms *)
  val var:      Sym.t -> term
  val asc:      tp -> term -> term
  val app:      term -> term -> term
  val proj:     int -> term -> term
  (* checking terms *)
  val lam:      Sym.t -> term -> term
  val tuple:    term list -> term
  (* transparent terms *)
  val letIn:    Sym.t -> term -> term -> term
end

module Frontend(Imp: BACKEND): FRONTEND = struct

  (* module type BACKEND = sig
   *   open Types
   *   type arrow
   *   val ident: 'a rep -> arrow
   *   val compose: arrow -> arrow -> arrow
   *   val pair: arrow -> arrow -> arrow
   *   val pi1: 'a rep -> 'b rep -> arrow
   *   val pi2: 'a rep -> 'b rep -> arrow
   *   val ignore: 'a rep -> arrow
   *   val lambda: arrow -> arrow
   *   val apply: 'a rep -> 'b rep -> arrow
   *   val in1: 'a rep -> 'b rep -> arrow
   *   val in2: 'a rep -> 'b rep -> arrow
   *   val case: arrow -> arrow -> arrow
   *   val absurd: 'a rep -> arrow
   * end *)
  open Types
  open Imp

  type tp = Types.tp
  type env = tp Env.t
  type term = env -> tp option -> tp * arrow

  exception Unbound of sym

  let var (name: sym) (env: env) (expect: tp option): tp * arrow =
    let got = try Env.find x env with Not_found -> raise Unbound in
    raise Unimplemented

  let asc _ = raise Unimplemented
  let app _ = raise Unimplemented
  let proj _ = raise Unimplemented
  let lam _ = raise Unimplemented
  let tuple _ = raise Unimplemented
  let letIn _ = raise Unimplemented
end

;; print_endline "hello"
