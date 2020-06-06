Class Symantics (repr : Type -> Type) :=
  {
  lnat : nat -> repr nat;
  lbool : bool -> repr bool;
  lam : forall {a b}, (repr a -> repr b) -> repr (a -> b);
  app : forall {a b},  repr (a -> b) -> repr a -> repr b;
  add : repr nat -> repr nat -> repr nat;
  mul : repr nat -> repr nat -> repr nat
  }.


Require Import Extraction.
Axiom Code : Type -> Type.
Extract Constant Code "'a" => "'a".



Axiom ocaml_lam : forall {a b: Type}, (Code a -> Code b) -> Code (a -> b).
Extract Inlined Constant ocaml_lam => "".
Axiom ocaml_app : forall {a b : Type},  Code (a -> b) -> Code a -> Code b.
Extract Inlined Constant ocaml_app => "".

Axiom ocaml_let : forall a b, a -> (a -> b) -> b.
Extract Constant ocaml_let => "(fun x f -> f x)".

Axiom ocaml_add : Code nat -> Code nat -> Code nat.
Extract Inlined Constant ocaml_add => "(+)".
Axiom ocaml_mul : Code nat -> Code nat -> Code nat.
Extract Inlined Constant ocaml_mul => "(*)".

(* lift is also a return instance for Code? *)
Axiom lift : forall {a : Type}, a -> Code a.
Extract Inlined Constant lift => "(*lift*)".
Check ocaml_app.
Check ocaml_lam.

Instance codesym : Symantics Code := {|
  lnat := lift;
  lbool := lift;
  lam := fun a b => ocaml_lam (a := a) (b := b);
  app := fun a b => ocaml_app (a := a) (b := b);
  add := ocaml_add;
  mul := ocaml_mul
                                    |}.

(* Might be interesting to try and use this. Too cute? *)
Definition R (x : Type) := x.

(* Need seperate definition to help type inference *)
Definition lamhelper (a b : Type) (f : R a -> R b) : R (a -> b) :=
  fun (x : a) => f x.

Instance regularsym' : Symantics R := {|
  lnat := fun x => x;
  lbool := fun x => x;
  lam := lamhelper;
  app := fun _ _ f x => f x;
  add := fun x y => x + y;
  mul := fun x y => x * y;
                                     |}.

Record Partial s d :=
  {
  dyn : Code d;
  sta : option s
  }.
Arguments dyn {s} {d}.
Arguments sta {s} {d}.

Class StaticT (a : Type) := {staticT : Type}.

Arguments staticT {a}.

Instance arrstat {a b : Type} `{sa : StaticT a} `{sb : StaticT b} : StaticT (a -> b) | 0 :=
  {| staticT := Partial sa.(staticT) a ->  Partial sb.(staticT) b |}.

(*
Instance genstat {a} : Stat a | 50 := {| stat := a |}.
*)

Instance natstat : StaticT nat  := {| staticT := nat |}.

Definition abstr {s d} : Partial s d -> Code d := dyn.
Definition pdyn {s d} (x : Code d) : Partial s d := {| sta := None; dyn := x |}.

Definition quote {s d} : Partial s d -> Code d := abstr.
Definition splice {s d} (x : Code d) : Partial s d := pdyn x.

Definition plam {a b} `{sa : StaticT a} `{sb : StaticT b} (f : Partial sa.(staticT) a -> Partial sb.(staticT) b) :
  Partial _ (* ( DynSta2 sa.(stat) a -> DynSta2 sb.(stat) b)*) (a -> b)  :=
  {| dyn := ocaml_lam (fun x => abstr ( f (pdyn x) ));
    sta := Some f
  |}.

Definition papp {a b : Type} `{sa : StaticT a} `{sb : StaticT b} (ef : Partial _ (a -> b)) (ea : Partial (staticT sa) a ) : Partial (staticT sb) b :=
  match (sta ef) with
  | Some f => f ea
  | _ => pdyn ( ocaml_app (abstr ef) (abstr ea) )
  end.

Definition pnat (n : nat) : Partial nat nat := {| dyn :=  lift n; sta := Some n |}.
Definition pbool (b : bool) : Partial bool bool := {| dyn :=  lift b; sta := Some b |}.

Definition padd (e1 e2 : Partial nat nat) : Partial nat nat :=
  match e1.(sta), e2.(sta) with
  | _ , Some O => e1
  | Some O , _ => e2
  | Some n, Some m => pnat (n + m)
  | _ , _ => pdyn (ocaml_add (abstr e1) (abstr e2))
  end.

Definition pmul (e1 e2 : Partial nat nat) : Partial nat nat :=
  match e1.(sta), e2.(sta) with
  | _ , Some O => pnat O
  | Some O , _ => pnat O
  | _ , Some (S O) => e1
  | Some (S O) , _ => e2
  | Some n, Some m => pnat (n * m)
  | _ , _ => pdyn (ocaml_mul (abstr e1) (abstr e2))
  end.



Eval cbv in  abstr (pdyn (abstr  (papp (plam (fun x => x)) (pnat 3)))).
Eval cbv in  quote  (papp (plam (fun x => x)) (pnat 3)). (* This is not a quote.*)


(*
Hmm. Not the right

Instance regularsym' `{StaticT s} : Symantics (Partial s) := {|
  lnat := fun x => x;
  lbool := fun x => x;
  lam := lamhelper;
  app := fun _ _ f x => f x;
  add := fun x y => x + y;
  mul := fun x y => x * y;
                                     |}.

*)
