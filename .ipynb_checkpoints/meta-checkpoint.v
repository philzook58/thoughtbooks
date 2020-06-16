
Class Symantics (repr : Type -> Type) := {
  lnat : nat -> repr nat;
  lbool : bool -> repr bool;
  lam : forall a b, (repr a -> repr b) -> repr (a -> b);
  app : forall a b,  repr (a -> b) -> repr a -> repr b;                                                   

                                        }.

Record R a := { unR : a }.
Arguments Build_R {a}.
Arguments unR {a}.
Check Build_R.
Check Build_R.
Instance regularsym : Symantics R := {|
  lnat := Build_R;
  lbool := Build_R;
  lam := fun a b f => Build_R (fun x => unR (f (Build_R (a:= a) x)));
  app := fun _ _ f x => Build_R ((unR f) (unR x))
                                    |}.


Definition thing {repr : Type -> Type} `{Symantics repr} : repr nat := lnat 3.


Require Import Extraction.
Axiom Code : Type -> Type.
Extract Constant Code "'a" => "'a".
Axiom ocaml_lnat : nat -> Code nat.
Extract Inlined Constant ocaml_lnat => "".

Axiom ocaml_lbool : bool -> Code bool.
Extract Constant ocaml_lbool => "fun x -> x".

Axiom ocaml_lam : forall {a b: Type}, (Code a -> Code b) -> Code (a -> b).
Extract Inlined Constant ocaml_lam => "".
Axiom ocaml_app : forall {a b : Type},  Code (a -> b) -> Code a -> Code b.
Extract Inlined Constant ocaml_app => "".

(* pcaml_lam opacifies a function. The function can never be applied inline becasue it is wrapped by ocaml_lam *)

Axiom ocaml_lam' : forall a b, (Code a -> Code b) -> Code (a -> b).
Extract Inlined Constant ocaml_lam' => "". (* This seems questionable. There is no way the ocaml compiler doesn't compile those identity function away right? *)
Arguments ocaml_lam' {a} {b}.

(* This is an applicative apply

Maybe being applicative makes the most conceptual sense. We can't inspect Code values to change control flow in some sense. Although obviously we do at compile time. I'm not sure.
 *)


Axiom ocaml_let : forall a b, a -> (a -> b) -> b.
Extract Constant ocaml_let => "(fun x f -> f x)".

Axiom ocaml_add : Code nat -> Code nat -> Code nat.
Extract Inlined Constant ocaml_add => "(+)".
Axiom ocaml_mul : Code nat -> Code nat -> Code nat.
Extract Inlined Constant ocaml_mul => "(*)".
(*
Definition test {a b} := ocaml_lam' a _ (fun x => (ocaml_lam' b _ (fun y => x))).
Definition test2 {a b} := ocaml_lam' _ _ (fun x => (ocaml_lam' a _ (fun y => ocaml_app _ b x y))).
*)

Definition ex1 : Code nat := ocaml_add (ocaml_lnat 1) (ocaml_lnat 2).
Extraction ex1.

Definition splice_ex (c : Code nat) : Code nat := ocaml_mul c (ocaml_lnat 10).
Definition sp := Eval cbv in (splice_ex ex1).
Extraction sp.

Fixpoint simple_pow (n: nat) (x : nat) : nat :=
  match n with
  | O => 1
  | S n' => x * (simple_pow n' (pred x))
  end.
Fixpoint pow' (n: nat) : Code (nat -> nat) :=
  match n with
  | O => ocaml_lam' (fun _ => ocaml_lnat 1)
  | S n' => ocaml_lam' (fun x => ocaml_mul x (ocaml_app (pow' n') x)) (* ocaml_mul x (simple_pow n' (pred x)) *)
  end.
Fixpoint pow'' (n: nat) (x : Code nat) : Code nat :=
  match n with
  | O => ocaml_lnat 1
  | S n' => ocaml_mul x (pow'' n' x) (* ocaml_mul x (simple_pow n' (pred x)) *)
  end.

Definition pow''' (n : nat) : Code (nat -> nat) :=
  ocaml_lam (fun x => (pow'' n x)).

Definition pow4''' := Eval cbv in pow''' 4.
Definition pow4' := Eval cbv in pow' 4.
Extraction pow4'.
Extraction pow4'''. (* Is much much nicer *)


(* But really lift could just be an axiom 
Unless guarding it important for some reason?

Axiom quote : a -> Code a 
No this isn't right because I have nothing that'll recursively do it





 *)



Axiom World : Type.
Extract Constant World => "unit".

Axiom ref : Type -> Type.
Extract Constant ref "'a" => "'a ref".
(* make_ref     =>     "ref*)
Axiom get_ref : forall a, ref a -> World -> a * World.
Extract Constant get_ref => "fun r _ -> (!r  ,())".
Axiom set_ref : forall a, ref a -> a -> World -> unit * World.
Extract Constant set_ref => "fun r x _ -> let () = r := x in (() , ())".


Axiom Array : Type -> Type.
Extract Constant Array "'a" => "'a array".

Axiom make : forall {a : Type}, Code nat -> Code a -> Code World -> Code (Array a  *  World).



Axiom ocaml_fst : forall {a b : Type}, Code (a * b) -> Code a.


(* What difference does it make to have these be code or not?
Or to have the whole thing wrapped in code?



   *)

Extract Constant make => "fun i def _ -> ( make i def , ())".
Axiom get : forall a, Array a -> nat -> World -> a * World.
Extract Constant get => "fun r i _ -> (r.(i)  ,())".
Axiom set : forall a, Array a -> nat -> a -> World -> unit * World.
Extract Constant set => "fun r i x _ -> let () = r.(i) <- x in (() , ())".




(*  Since World is not duplicable, I believe this is sound  *)

(* lift is also a return instance for Code. *)
Axiom lift : forall {a : Type}, a -> Code a.
Extract Inlined Constant lift => "(*lift*)".
Check ocaml_app.

Check (fun a b => fun (f : Code a -> Code b) => (lift f)).

(* Does this imply we getr a quote unquote from do notation? 
Can I write lam in terms oif lift and apply?




(Code a -> Code b) -> Code (a -> b)
fun f => ocaml_apply (lift f)


apply is applicative applu

lam is ~ inverse to apply

lam (fun x => apply f x) ~ f x ?

Are lam and apply in an adjunction?
it feels like they are pseudo inverses

Between static and dynamic cat?

(->s Code a  Code b ) -> (Code (->d a b))



  *)



(* ! *)

(*
Maybe we hsould just use IO monad discipline
It avoids the explciit unit that we're passing.
we get monad notation


can we derive a bind from lam lift and app?

Code a -> (a -> Code b) -> Code b
fun x f => 


Maybe Code is already sufficient and we don't need IO on top? Uh no. I think we could throw away effects

*)

Axiom for_ : nat -> nat -> (nat -> World -> World) -> World.
Extract Inlined Constant for_ => "(fun i j f -> for  k = i to j do (f k ()) done)   )".


(*

 

for loops
ocaml_for : nat -> nat -> (unit -> unit) -> unit




Class CSP a :=
  {
  lift : a -> Code a
  }.

Instance natcsp : CSP nat :=
  {|
    lift := ocaml_lnat
  |}.
*)


Axiom fix_ : forall {a : Type}, Code (a -> a) -> Code a.
(* Extract Inlined Constant fix_ *)
Definition plus2 (x : Code nat) (y : Code nat) : Code nat :=  ocaml_app (ocaml_app (lift plus) x) y.
Definition plustest := Eval cbv in  plus2 (lift 1) (lift 2).
Extraction plustest.
                                          

Definition pow5 : Code (nat -> nat -> nat) :=
  lift simple_pow. (* (let fix help := fun n x => match n with
                                   |  O => 1
                                   | S n =>  *)


Require Import Floats.

Open Scope float_scope.

Eval compute in 1 + 0.5.

Eval compute in 1 / 0.

Require Import ExtrOCamlFloats.
Definition foo : float := 1 + 0.5.
Extraction foo.
(*
Definition pow'''' : Code (nat -> nat -> nat) :=
  ocaml_lam (fun n => match n with
                      | O => ocaml_lam (fun _ => ocaml_lnat 1)
                      | S n' => ocaml_lam (fun x => ocaml_mul x (ocaml_app (ocaml_app pow'' n') x))
                      end)
.


(*

The ocaml compiler is surprisngly literal
On godbolt , the flambda compiler is msart enough to survive some abstractions and give indetical cdoe



let cumsum (x : unit) : int =
   let acc = ref 0 in
   for i = 0 to 10 do
      acc := !acc + i
    done;
    !acc

let for_ m n k =  for i = m to n do k i done




let cumsum2 (x : unit) : int =
   let acc = ref 0 in
    for_ 0 10 (fun i -> acc := !acc + i) ;
    !acc

    (*  These two ouptut identical code for flambda
    flambda also doesn't allocate for the closure version of acc
    I think flambda also removes unnecceary units
    flambd inlines is smart
    *)

*)






(* No. There isn't a way to write this, right?
The Axioms form a "data type" for Code, however, one that can't be inspected.
So we need a node for + right?

ocaml_app (lift (+))

Definition plus2 : Code nat -> Code nat -> Code nat :=  ocaml_lam (fun x => (ocaml_lam (fun y =>   b
*)

Definition plus2 := ocaml_app (ocaml_app (lift (+))). 
Definition pow7 := Eval cbv in pow'''' 7.
Extraction pow7.







Definition test3 := ocaml_lam' _ _ (fun x => (ocaml_lam' _ _ (fun y => ocaml_add x y))).
Extraction test.
Extraction test2.
Definition t3 := Eval cbv in ocaml_app _ _ test3 (ocaml_lnat 3).
Extraction t3.
(* No. this is impossible *)



(*

Great. Beautiful.
But now we want to be able to use quote and splice annotations and not have to rewrite everything

So we need both Code and not code versions of things.

if I quote -> just the code version




if I splice

At lambda creattion time it isn't clear if it's gonna be frozen out,



*)
*)

(*
Instance codesym : Symantics Code := {|
  lnat := ocaml_lnat;
  lbool := ocaml_lbool;
  lam := ocaml_lam;
  app := ocaml_app
  |}.
*)
Record DynSta a := {
  
  sta : option a;
  dyn : Code a

                  }.

Arguments sta {a}.
Arguments dyn {a}.

Inductive DynStaaa := dyn : a -> | Code 

                                     (*  a -> b, Code a -> Code b --> DynSta (a -> b) *)
Definition lambdy {a b} ( f : DynSta a -> DynSta b) : DynSta (a -> b) :=
  {| sta := Some {|  f  |} ; dyn := ocaml_lam (fun x => dyn ( f {| sta := None ; dyn := x |}))  |}.


(*
As some kinda gadt
Inductive ReflDynsta :=
| Recurse : option (ReflDynsta a -> ReflDynsta b) -> Code (a -> b) -> ReflDynatsa (a -> b)
                                                                                  | Done : option a -> Code a -> ReflDynsta a


using typeclass directed stuff
Instance DynSta (a -> b) :=
Instance DynSta a | 100 := 



Instance dynsta : Symantics DynSta := {|
  lnat := fun n => Build_DynSta (Some (lnat n)) (lnat n);
  lbool := fun n => Build_DynSta (Some (lbool n)) (lbool n);
  lam := fun a b f =>  Build_DynSta (Some f) ( f )                       
  
  |}.


We want a data type that holds recusrively all the possible places Code could be placed in a lambda.

If we had such a thing we could 

Quote  -> take the code part

Split -> take the dynamic part (1 layer)

 

Definition lambo {a b} (f : DynSta a -> DynSta b) : DynSta (a -> b)  :=  {|  sta := fun x =>  match f.(sta) with | None => None | Some f' =>  ; dyn := ocaml_lam f.(dyn)   |}.

 *)


Record DynSta2 s d :=
  {
  dyn2 : Code d;
  sta2 : option s
  }.
Arguments dyn2 {s} {d}.
Arguments sta2 {s} {d}.

Class Stat (a : Type) := {stat : Type}.

Arguments stat {a}.

Instance arrstat {a b : Type} `{sa : Stat a} `{sb : Stat b} : Stat (a -> b) | 0 :=
  {| stat := DynSta2 sa.(stat) a ->  DynSta2 sb.(stat) b |}.

(*
Instance genstat {a} : Stat a | 50 := {| stat := a |}.
*)

Instance natstat : Stat nat  := {| stat := nat |}.


Definition abstr {s d} : DynSta2 s d -> Code d := dyn2.
Definition pdyn {s d} (x : Code d) : DynSta2 s d := {| sta2 := None; dyn2 := x |}.


(*

This typeclass stuff is pushin it and 


The partial evaluator they show is a particular kind of partiasl evluator

lambo := Dyn


quote (x : DynSta) = {| None;  x.dyn |} ?? Or does nothing?
splice  removes one layer of code
*)

Definition lambo {a b} `{sa : Stat a} `{sb : Stat b} (f : DynSta2 sa.(stat) a -> DynSta2 sb.(stat) b) :
  DynSta2 _ (* ( DynSta2 sa.(stat) a -> DynSta2 sb.(stat) b)*) (a -> b)  :=
  {| dyn2 := ocaml_lam (fun x => abstr ( f (pdyn x) ));
    sta2 := Some f
  |}.

Print lambo.

Definition appbo {a b : Type} `{sa : Stat a} `{sb : Stat b} (ef : DynSta2 _ (a -> b)) (ea : DynSta2 (stat sa) a ) : DynSta2 (stat sb) b :=
  match (sta2 ef) with
  | Some f => f ea
  | _ => pdyn ( ocaml_app (abstr ef) (abstr ea) )
end.


(* This is not following the definitions in the paper. *)
(*
Definition addbo : DynSta2 _ (nat -> nat -> nat) := {| dyn2 := ocaml_lam (fun x => ocaml_lam (fun y => ocaml_app (ocaml_app (lift plus) x) y)) ; sta2 := Some plus |}.
 *)

(*
Definition addbo (x : DynSta2 _ nat) ( y : DynSta2 _ nat) : DynSta2 _ nat :=
  match (sta2 x), (sta2 y) with
  | Some 0, e | e, Some 0 => e
  | Some n, Some n => i


We could make the second type parameter to Dynsta2 always inferred


everything hjas horrible names. At what point is that nbo longer funny?


*)

Arguments DynSta2 {s}.
Print addbo.
Check appbo. (* Now this specialzies.. hmm.*)

Set Typeclasses Debug.
Fixpoint addem (n : nat) : DynSta2 nat nat :=
  match n with
    | O => pdyn (lift O)
    | S n' => appbo addbo (pdyn (lift n)) (addem n')
  end.


Print appbo.



(*
Not happy about this?
Check appbo. 

What about insaetad of using a typeclass we used 

DynSta3 s a :=
{|
  st : Type;
  sta : option st;
  dyn : Code a
  
|}




*)

Definition testy {a} : DynSta2 _ (a -> a) := lambo (fun x => x).
Print testy.
Eval cbv in testy.


Class Quoter (a : Type) := {
  stat : Type;
  abstr : DynSta2 stat a -> Code a;
  pdyn : Code a -> Dynsta2 stat a;
  lambo : forall {a b : Type}, forall `{qa : Quoter a}, forall `{qb : Quoter b}, (Dynsta2 qa.(stat) a -> Dynsta2 b) -> Dynsta2 (a -> b);
  (* appbo : forall {a b}, `{Quoter  } -> Dynsta2 (a -> b) -> (Dynsta2 a -> Dynsta2 b). *)
  }.


Instance Quoter (a -> b) 


