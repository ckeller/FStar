module Lang

open FStar.Seq
open FStar.Set
open FStar.Classical
open FStar.Buffer
open FStar.Seq

open FStar.ST
open FStar.Heap  //this order of opening the modules is important, we want ref from FStar.Heap

open FStar.Tactics

#set-options "--lax"

type addr = ref int

let equal (h1:heap) (h2:heap) =
  (forall (r:addr). (h1 `contains` r) <==> (h2 `contains` r)) /\
  (forall (r:addr). (h1 `contains` r) /\ (h2 `contains` r) ==> (sel h1 r == sel h2 r))
  
type loop_result (a:Type0) =
  | Done : v:a   -> loop_result a
  | Again: acc:a -> loop_result a

noeq type command :Type0 -> Type =
  | Return: #a:Type -> v:a -> command a
  | Bind  : #a:Type0 -> #b:Type0 -> c1:command a -> c2:(a -> command b) -> command b
  //| Loop  : #a:Type0 -> acc:a -> f:(a -> command (loop_result a)) -> command a
  //| Fail  : #a:Type0 -> command a
  | Read  : id:addr -> command int
  | Write : id:addr -> v:int -> command unit
  | Alloc : command addr
  //| Free  : id:addr -> command unit

(*
 * a bit hacky, since a program may not termiinte
 *)
assume val interpreted_in (#a:Type0) (c:command a) (h:heap) :Tot (a * heap)

type heap_predicate = heap -> Type0

let is_emp (h:heap) : Type0 = (h == emp)

let points_to (id:addr) (n:int) (h:heap) : Type0 =
  (h == (restrict h (Set.singleton (addr_of id)))) /\ (sel h id == n)

let lift (phi:Type0) (h:heap) :Type0 = phi /\ is_emp h

let exists_x (#a:Type0) (pred:a -> heap_predicate) (h:heap) :Type0
  = exists (x:a). pred x h

let star (p:heap_predicate) (q:heap_predicate) (h:heap) :Type0
  = exists (h1:heap) (h2:heap). disjoint h1 h2 /\ (h == (join h1 h2)) /\ p h1 /\ q h2

let iff (p:heap_predicate) (q:heap_predicate) :Type0 = forall (h:heap). p h <==> q h

let imp (p:heap_predicate) (q:heap_predicate) :Type0 = forall (h:heap). p h ==> q h

type c_pre            = heap_predicate
type c_post (a:Type0) = a -> heap_predicate

type hoare_triple (#a:Type0) (pre:c_pre) (c:command a) (post:c_post a)
  = forall (h0:heap) (h1:heap) (r:a). (pre h0 /\ (c `interpreted_in` h0 == (r, h1))) ==> post r h1

let rec wp_command (#a:Type0) (c:command a) (p:st_post a) (h0:heap) :Type0
  = match c with
    | Return #a x      -> p x h0
    | Bind #a #b c1 c2 ->
      FStar.Classical.forall_intro (FStar.WellFounded.axiom1 #a #(command b) c2);
      (wp_command c1) (fun x h1 -> (wp_command (c2 x)) p h1) h0
    //| Loop #_ _ _      -> False
    //| Fail #_          -> True
    | Read r           -> p (sel h0 r) h0
    | Write r x        -> (forall (h1:heap). (sel h1 r == x /\ modifies !{r} h0 h1) ==> p () h1)
    | Alloc            -> (forall (r:ref int) (h1:heap). (fresh r h0 h1 /\ modifies !{} h0 h1 /\ sel h1 r == 0) ==> p r h1)
    //| Free r           -> False

let disjoint_partitions (h:heap) (h1:heap) (h2:heap) :Type0 = disjoint h1 h2 /\ h == h1 `join` h2

let rec wpsep_command (#a:Type0) (c:command a) :st_wp a
  = match c with
    | Return #a x      -> fun p h0 -> h0 == emp /\ p x h0

    | Bind #a #b c1 c2 ->
      FStar.Classical.forall_intro (FStar.WellFounded.axiom1 #a #(command b) c2);
      fun p h3 -> exists (h2' h2'':heap). (disjoint_partitions h3 h2' h2'') /\
                                  (wp_command c1) (fun x h1 -> exists h1' h1''. (disjoint h1' h1'' /\ disjoint h1 h2'' /\
			                                                 h1' `join` h1'' == h1 `join` h2'')
						                      /\ (wp_command (c2 x)) (fun y h2 -> h2 `disjoint` h1'' /\ p y (h2 `join` h1'')) h1') h2'
      

    | Read r    -> fun p h0 -> (exists x. points_to r x h0) /\ (forall x. points_to r x h0 ==> p x h0)

    | Write r y -> fun p h0 -> (exists x. points_to r x h0) /\ (forall h1. points_to r y h1 ==> p () h1)

    | Alloc     -> fun p h0 -> h0 == emp /\ (forall r h1. points_to r 0 h1 ==> p r h1)

let lift_wpsep (#a:Type0) (wp_sep:st_wp a) :st_wp a
  = fun p h0 -> exists h0' h0''. disjoint h0' h0'' /\ h0 == h0' `join` h0'' /\
                         wp_sep (fun x h1' -> disjoint h1' h0'' /\ p x (h1' `join` h0'')) h0'

let steps :list step = [delta_only
  ["Lang.wp_command";
   "Lang.wpsep_command";
   "Lang.lift_wpsep";
   "Lang.disjoint_partitions";
   "Lang.uu___is_Return";
   "Lang.uu___is_Bind";
   "Lang.uu___is_Read";
   "Lang.uu___is_Write";
   "Lang.uu___is_Alloc";
   "Lang.__proj__Return__item__v";
   "Lang.__proj__Bind__item__c1";
   "Lang.__proj__Bind__item__c2";
   "Lang.__proj__Read__item__id";
   "Lang.__proj__Write__item__id";
   "Lang.__proj__Write__item__v";
   "Lang.c1";
   "Lang.bind"];

   zeta; iota; primops
  ]

#reset-options "--z3rlimit 5"
(* get the nice x <-- c1; c2 syntax *)
//let bind (#a:Type0) (#b:Type0) (c1:command a) (c2:a -> command b) :command b = Bind c1 c2

let unfold_fns :list string = [
  "wp_command"; "wpsep_command"; "lift_wpsep"; "disjoint_partitions"; "uu___is_Return"; "uu___is_Bind";
  "uu___is_Read"; "uu___is_Write"; "uu___is_Alloc"; "__proj__Return__item__v";
   "__proj__Bind__item__c1"; "__proj__Bind__item__c2"; "__proj__Read__item__id";
   "__proj__Write__item__id"; "__proj__Write__item__v"
  ]

unfold let unfold_steps =
  List.Tot.map (fun s -> pack_fv ["Lang"; s]) unfold_fns

let foo (r1:addr) (r2:addr) (h:heap{sel h r2 == 4 /\ addr_of r1 <> addr_of r2})
  = let c = Bind (Write r1 3) (fun _ -> Read r1) in
    let p :st_post int = fun _ h -> sel h r2 == 4 in
    let t = (lift_wpsep (wpsep_command c)) p h in
    assert_by_tactic t (norm [Delta; UnfoldOnly unfold_steps; Primops];; dump "Foo")



exists h0' h0''. h == h0' `join` h0'' /\
                 (exists h2' h2''. h0' == h2' `join` h2'' /\
                                   (forall h1. sel h1 r1 == 3 ==>
                                               (exists h1' h1''. h1' `join` h1'' == h1 `join` h2'' /\
                                                                 sel ((h1' `join` h1'') `join` h0'') r2 == 4)))





    assert_by_tactic t (norm [Delta; UnfoldOnly [pack_fv ["Lang"; "wp_command"];
                                                 pack_fv ["Lang"; "wpsep_command"];
						 pack_fv ["Lang"; "disjoint_partitions"];
						 pack_fv ["Lang"; "uu___is_Return"];
						 pack_fv ["Lang"; "uu___is_Bind"];
						 pack_fv ["Lang"; "uu___is_Read"];
						 pack_fv ["Lang"; "uu___is_Write"];
						 pack_fv ["Lang"; "uu___is_Alloc"];
						 pack_fv ["Lang"; "__proj__Return__item__v"];
						 pack_fv ["Lang"; "__proj__Bind__item__c1"];
						 pack_fv ["Lang"; "__proj__Bind__item__c2"];
						 pack_fv ["Lang"; "__proj__Read__item__id"];
						 pack_fv ["Lang"; "__proj__Write__item__id"];
						 pack_fv ["Lang"; "__proj__Write__item__v"];
						 ];
			      Primops])

(* #set-options "--z3rlimit 10" *)
(* let foo (r1:addr) (n1:int) *)
(*         (r2:addr) (n2:int) *)
(*         (r3:addr) (n3:int) *)
(*         (r4:addr) (n4:int) *)
(*         (r5:addr) (n5:int) *)
(*         (r6:addr) (n6:int) *)
(*         (h:heap{distinct_and_contained r1 r2 r3 r4 r5 r6 h}) *)
(*   =  let p1  :st_post int = fun _ h -> sel h r1 == n1 + 6 /\ sel h r2 == n6 /\ sel h r3 == n5 /\ sel h r4 == n4 /\ sel h r5 == n5 /\ sel h r6 == n6 *)
(*      in *)

(*      let t  = wp_command (c1 r1 n1 r2 n2 r3 n3 r4 n4 r5 n5 r6 n6) p1 h in *)
(*      assert (Prims.norm steps t) *)

(* (\* let distinct_and_contained (r1:addr) (r2:addr) (r3:addr) (r4:addr) (r5:addr) (r6:addr) (h:heap) *\) *)
(* (\*   = addr_of r1 <> addr_of r2 /\ addr_of r1 <> addr_of r3 /\ addr_of r1 <> addr_of r4 /\ addr_of r1 <> addr_of r5 /\ addr_of r1 <> addr_of r6 /\ *\) *)
(* (\*     addr_of r2 <> addr_of r3 /\ addr_of r2 <> addr_of r4 /\ addr_of r2 <> addr_of r5 /\ addr_of r2 <> addr_of r6 /\ *\) *)
(* (\*     addr_of r3 <> addr_of r4 /\ addr_of r3 <> addr_of r5 /\ addr_of r3 <> addr_of r6 /\ *\) *)
(* (\*     addr_of r4 <> addr_of r5 /\ addr_of r4 <> addr_of r6 /\ *\) *)
(* (\*     addr_of r5 <> addr_of r6 /\ *\) *)
(* (\*     h `contains` r1 /\ h `contains` r2 /\ h `contains` r3 /\ h `contains` r4 /\ h `contains` r5 /\ h `contains` r6 *\) *)

(* (\* let c1 (r1:addr) (n1:int) *\) *)
(* (\*        (r2:addr) (n2:int) *\) *)
(* (\*        (r3:addr) (n3:int) *\) *)
(* (\*        (r4:addr) (n4:int) *\) *)
(* (\*        (r5:addr) (n5:int) *\) *)
(* (\*        (r6:addr) (n6:int) *\) *)
(* (\*   :command int *\) *)
(* (\*   = Write r1 n1;; *\) *)
(* (\*     n <-- Read r1; *\) *)
(* (\*     r <-- Alloc; *\) *)
(* (\*     Write r2 n2;; *\) *)
(* (\*     Write r3 n3;; *\) *)
(* (\*     Write r4 n4;; *\) *)
(* (\*     Write r5 n5;; *\) *)
(* (\*     Write r6 n6;; *\) *)
(* (\*     Write r n1;; *\) *)
(* (\*     Write r1 (n + 1);; *\) *)
(* (\*     n <-- Read r1; *\) *)
(* (\*     r <-- Alloc; *\) *)
(* (\*     Write r2 n6;; *\) *)
(* (\*     Write r3 n5;; *\) *)
(* (\*     Write r4 n4;; *\) *)
(* (\*     Write r5 n5;; *\) *)
(* (\*     Write r6 n6;; *\) *)
(* (\*     Write r n5;; *\) *)
(* (\*     Write r1 (n + 1);; *\) *)
(* (\*     n <-- Read r1; *\) *)
(* (\*     r <-- Alloc; *\) *)
(* (\*     Write r2 n2;; *\) *)
(* (\*     Write r3 n3;; *\) *)
(* (\*     Write r4 n4;; *\) *)
(* (\*     Write r5 n5;; *\) *)
(* (\*     Write r6 n6;; *\) *)
(* (\*     Write r n3;; *\) *)
(* (\*     Write r1 (n + 1);; *\) *)
(* (\*     n <-- Read r1; *\) *)
(* (\*     r <-- Alloc; *\) *)
(* (\*     Write r2 n6;; *\) *)
(* (\*     Write r3 n5;; *\) *)
(* (\*     Write r4 n4;; *\) *)
(* (\*     Write r5 n5;; *\) *)
(* (\*     Write r6 n6;; *\) *)
(* (\*     Write r n5;; *\) *)
(* (\*     Write r1 (n + 1);; *\) *)
(* (\*     n <-- Read r1; *\) *)
(* (\*     Write r2 n2;; *\) *)
(* (\*     Write r3 n3;; *\) *)
(* (\*     Write r4 n4;; *\) *)
(* (\*     Write r5 n5;; *\) *)
(* (\*     Write r6 n6;; *\) *)
(* (\*     Write r1 (n + 1);; *\) *)
(* (\*     n <-- Read r1; *\) *)
(* (\*     r <-- Alloc; *\) *)
(* (\*     Write r2 n6;; *\) *)
(* (\*     Write r3 n5;; *\) *)
(* (\*     Write r4 n4;; *\) *)
(* (\*     Write r5 n5;; *\) *)
(* (\*     Write r6 n6;; *\) *)
(* (\*     Write r n1;; *\) *)
(* (\*     Write r1 (n + 1);; *\) *)
(* (\*     Return 0 *\) *)
  
(* (\* let steps :list step = [delta_only *\) *)
(* (\*   ["Lang.wp_command"; *\) *)
(* (\*    "Lang.uu___is_Return"; *\) *)
(* (\*    "Lang.uu___is_Bind"; *\) *)
(* (\*    "Lang.uu___is_Read"; *\) *)
(* (\*    "Lang.uu___is_Write"; *\) *)
(* (\*    "Lang.uu___is_Alloc"; *\) *)
(* (\*    "Lang.__proj__Return__item__v"; *\) *)
(* (\*    "Lang.__proj__Bind__item__c1"; *\) *)
(* (\*    "Lang.__proj__Bind__item__c2"; *\) *)
(* (\*    "Lang.__proj__Read__item__id"; *\) *)
(* (\*    "Lang.__proj__Write__item__id"; *\) *)
(* (\*    "Lang.__proj__Write__item__v"; *\) *)
(* (\*    "Lang.c1"; *\) *)
(* (\*    "Lang.bind"]; *\) *)

(* (\*    zeta; iota; primops *\) *)
(* (\*   ] *\) *)

(* (\* #reset-options *\) *)

(* (\* #set-options "--z3rlimit 10" *\) *)
(* (\* let foo (r1:addr) (n1:int) *\) *)
(* (\*         (r2:addr) (n2:int) *\) *)
(* (\*         (r3:addr) (n3:int) *\) *)
(* (\*         (r4:addr) (n4:int) *\) *)
(* (\*         (r5:addr) (n5:int) *\) *)
(* (\*         (r6:addr) (n6:int) *\) *)
(* (\*         (h:heap{distinct_and_contained r1 r2 r3 r4 r5 r6 h}) *\) *)
(* (\*   =  let p1  :st_post int = fun _ h -> sel h r1 == n1 + 6 /\ sel h r2 == n6 /\ sel h r3 == n5 /\ sel h r4 == n4 /\ sel h r5 == n5 /\ sel h r6 == n6 *\) *)
(* (\*      in *\) *)

(* (\*      let t  = wp_command (c1 r1 n1 r2 n2 r3 n3 r4 n4 r5 n5 r6 n6) p1 h in *\) *)
(* (\*      assert (Prims.norm steps t) *\) *)