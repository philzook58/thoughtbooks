
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
Extract Constant ocaml_lnat => "fun x -> x".

Axiom ocaml_lbool : bool -> Code bool.
Extract Constant ocaml_lbool => "fun x -> x".

Axiom ocaml_lam : forall a b, (Code a -> Code b) -> Code (a -> b).
Extract Inlined Constant ocaml_lam => "(fun f -> f)".
Axiom ocaml_lam' : forall a b, (Code a -> Code b) -> Code (a -> b).
Extract Inlined Constant ocaml_lam' => "". (* This seems questionable. There is no way the ocaml compiler doesn't compile those identity function away right? *)
Axiom ocaml_app : forall a b,  Code (a -> b) -> Code a -> Code b.
Extract Constant ocaml_app => "(fun f x -> f x)".

Axiom ocaml_let : forall a b, a -> (a -> b) -> b.
Extract Constant ocaml_let => "(fun x f -> f x)".

Axiom ocaml_add : Code nat -> Code nat -> Code nat.
Extract Inlined Constant ocaml_add => "(+)".
Definition test {a b} := ocaml_lam' a _ (fun x => (ocaml_lam' b _ (fun y => x))).
Definition test2 {a b} := ocaml_lam' _ _ (fun x => (ocaml_lam' a _ (fun y => ocaml_app _ b x y))).
Definition test3 := ocaml_lam' _ _ (fun x => (ocaml_lam' _ _ (fun y => ocaml_add x y))).
Extraction test.
Extraction test2.
Definition t3 := Eval cbv in ocaml_app _ _ test3 (ocaml_lnat 3).
Extraction t3.
(* No. this is impossible *)

Instance codesym : Symantics Code := {|
  lnat := ocaml_lnat;
  lbool := ocaml_lbool;
  lam := ocaml_lam;
  app := ocaml_app
  |}.

Record DynSta a := {
  
  sta : option (R a);
  dyn : Code a

                  }.


Defintion 

Instance dynsta : Symantics DynSta := {|
  lnat := fun n => Build_DynSta (Some (lnat n)) (lnat n);
  lbool := fun n => Build_DynSta (Some (lbool n)) (lbool n);
  lam := fun a b f =>  Build_DynSta (Some f) (  )                       
  
  |}.






