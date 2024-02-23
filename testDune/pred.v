
Set Universe Polymorphism.
Set Primitive Projections.

Record Sum@{q |a b|} (A : Type@{q|a}) (B : A -> Type@{q|b}) : Type@{q | max(a,b)} :=
  pair { fst : A ; snd : B fst }.

Inductive Id@{a|} {A : Type@{a}} (x : A) : A -> Type@{a} := refl : Id x x.
Notation "x ≡ y" := (Id x y) (at level 65).

Definition eq_Id {A} {x y : A} : x = y -> x ≡ y.
Proof. now intros ->. Qed.

Sort pred.
(* Should be a notation *)
Definition Pred@{u} := Type@{pred|u}.

Symbol base@{u} : Pred@{u} -> Type@{u}.
Symbol fib@{u} : forall (A : Pred@{u}), base A -> Type@{u}.

Symbol poly@{u} : forall (A : Type@{u}), (A -> Type@{u}) -> Pred@{u}.

Rewrite Rule base_poly := base (poly ?A ?B) ==> ?A.
Rewrite Rule fib_poly := fib (poly ?A ?B) ==> ?B.

(* If needs be, we can impose an extensionality axiom on any Pred *)
(* Axiom poly_base_fib@{u +} : forall (A : Pred@{u}), poly (base A) (fib A) ≡ A. *)

Definition P : Pred := poly unit (fun _ => False).

Definition shiromaru (A : Pred) := P -> A.

Definition is_kuro (A : Pred) := forall x y : base A, x ≡ y.


Class PredStruct@{u} (A : Pred@{u}) := { baseStr : Type@{u}  ; fibStr : baseStr -> Type@{u} }.

Arguments baseStr : clear implicits.
Arguments baseStr _ & {_}.
Arguments fibStr : clear implicits.
Arguments fibStr _ & {_} _.

Instance default_pred_struct@{u} {A : Pred@{u}} : PredStruct@{u} A | 100 := 
  {| baseStr := base A ; fibStr  := fib A |}.

Instance arr_pred_struct@{u} {A B : Pred@{u}} 
  `{pA : PredStruct@{u} A} `{pB : PredStruct@{u} B} 
  : PredStruct@{u} (A -> B) :=
  {| 
    baseStr := baseStr A -> baseStr B ; 
    fibStr f := forall a, fibStr A a -> fibStr B (f a)
  |}.

Symbol depBase@{u} : forall {A : Pred@{u}} (B : A -> Pred@{u}), base A -> Type@{u}.
Symbol depFib@{u} : forall (A : Pred@{u}) (a : base A), fib A a -> Type@{u}.

Rewrite Rule foo := @depBase ?A ?B ?a ==> 

Class DepPredStruct@{u} {A : Pred@{u}} `{PredStruct A} (B : A -> Pred@{u}) := 
  { depBaseStr : baseStr A -> Type@{u}  ; 
    depFibStr : forall a, fibStr A a -> Type@{u} }.

Instance: DepPredStruct@{u}

Instance dependent_pred_struct@{u} {A : Pred@{u}} :
  PredStruct@{u} (A -> Pred@{u})


