Set Primitive Projections.
Set Universe Polymorphism.
Set Printing Universes.

(* Standard sigma type with primitive projections *)
Cumulative Polymorphic Record sigma {A : Type} {B : A -> Type} :=
  pair { π1 : A ; π2 : B π1 }.
Arguments sigma : clear implicits.
Notation "'∑' x .. y ',' B" := (sigma _ (fun x => .. (sigma _ (fun y => B)) .. )) (at level 50, x binder, y binder, B at level 100).

(* I axiomatize the two injectivity rules on equalities ∑ A1 B1 ~ ∑ A2 B2
   following the rules for observational TT.
   The duplication of universe levels u1/u2 and the additional universe w instead of max(u1,u2,v1,v2)
   turned out to be useful in practice (c.f. hcastπ1' at the end of the file fails without the flexibility provided by w)
 *)
(* First injectivity rule corresponding to π1 *)
Axiom obseq_pair_0@{u1 u2 v1 v2 w} :
  forall (A1 : Type@{u1})
    (A2 : Type@{u2})
    (B1 : A1 -> Type@{v1})
    (B2 : A2 -> Type@{v2})
    (e : @obseq@{w+1}
           (Type@{w})
           (sigma@{u1 v1} A1 B1)
           (sigma@{u2 v2} A2 B2)),
    @obseq@{max(u1+1,u2+1)} (Type@{max(u1,u2)}) A1 A2.

(* Second injectivity rule corresponding to π2 *)
Axiom obseq_pair_1@{u1 u2 v1 v2 w} :
  forall (A1 : Type@{u1})
    (A2 : Type@{u2})
    (B1 : A1 -> Type@{v1})
    (B2 : A2 -> Type@{v2})
    (e : @obseq@{w+1}
           (Type@{w})
           (sigma@{u1 v1} A1 B1)
           (sigma@{u2 v2} A2 B2))
    (a1 : A1),
    let a2 := cast@{max(u1,u2)} A1 A2 (obseq_pair_0@{u1 u2 v1 v2 w} A1 A2 B1 B2 e) a1 in
    @obseq@{max(v1+1,v2+1)} Type@{max(v1,v2)} (B1 a1) (B2 a2).

(* Rewrite rule for π1 on a cast *)
Rewrite Rule obseq_pair :=
  | @{u1 u2 v1 v2 w} |-
      π1 (cast@{w}
            (sigma@{u1 v1} ?A1 ?B1)
            (sigma@{u2 v2} ?A2 ?B2)
            ?e
            ?p)
        >->
        cast@{max(u1,u2)} ?A1 ?A2 (obseq_pair_0@{u1 u2 v1 v2 w} ?A1 ?A2 ?B1 ?B2 ?e) (π1 ?p).

(* Rewrite rules complaining that this definition does not satisfy SR, but I think it does *)
(* Rewrite Rule obseq_pair2 := *)
(*   | @{u1 u2 v1 v2 w} |- *)
(*       π2 (cast@{w} *)
(*             (sigma@{u1 v1} ?A1 ?B1) *)
(*             (sigma@{u2 v2} ?A2 ?B2) *)
(*             ?e *)
(*             ?p) *)
(*         >-> *)
(*         cast@{max(v1,v2)} (?B1 (π1 ?p)) (?B2 _) (obseq_pair_1@{u1 u2 v1 v2 w} ?A1 ?A2 ?B1 ?B2 ?e (π1 ?p)) (π2 ?p). *)

(* intermediate helper definition for the rewrite rule of π2 on a cast *)
Definition obseq_pair_1'@{u1 u2 v1 v2 w} :
  forall (A1 : Type@{u1})
         (A2 : Type@{u2})
         (B1 : A1 -> Type@{v1})
         (B2 : A2 -> Type@{v2})
         (e : @obseq@{w+1}
                (Type@{w})
                (sigma@{u1 v1} A1 B1)
                (sigma@{u2 v2} A2 B2))
         (p1 : sigma@{u1 v1} A1 B1),
    let p2 := cast@{w} (sigma@{u1 v1} A1 B1) (sigma@{u2 v2} A2 B2) e p1 in
    @obseq@{max(v1+1,v2+1)} Type@{max(v1,v2)} (B1 (π1 p1)) (B2 (π1 p2)) :=
  fun A1 A2 B1 B2 e p1 => obseq_pair_1@{u1 u2 v1 v2 w} A1 A2 B1 B2 e (π1 p1).

(* Rewrite rule for π2 on a cast ; this time no complain about SR *)
Rewrite Rule obseq_pair2 :=
  | @{u1 u2 v1 v2 w} |-
      π2 (cast@{w}
            (sigma@{u1 v1} ?A1 ?B1)
            (sigma@{u2 v2} ?A2 ?B2)
            ?e
            ?p)
        >->
      cast@{max(v1,v2)} (?B1 (π1 ?p)) (?B2 _) (obseq_pair_1'@{u1 u2 v1 v2 w} ?A1 ?A2 ?B1 ?B2 ?e ?p) (π2 ?p).


(* SProp-valued Heterogenous equality (aka John Major equality) *)
Inductive jmeq@{s|a|?} (A : Type@{s|a}) (a : A) : forall (B : Type@{s|a}), B -> SProp :=
| jmrfl : jmeq A a A a.

Arguments jmeq {_} _ {_} _.
Arguments jmrfl {_} _.

(* The main useful task of jm equality: it absorbs casts *)
Lemma jm_cast_left {A B C} (AB : A ~ B) (a : A) (c : C) : jmeq a c -> jmeq (AB # a) c.
Proof. induction AB; trivial. Qed.

(* And we can derive an observational equality from the John Major one when the types of the lhs and rhs are observationally equal *)
Lemma from_jm {A B} (e : A ~ B) {a : A} {b : B} : jmeq a b -> e # a ~ b.
Proof. intros h; now induction h. Qed.

(* In particular, when the types of the lhs and rhs are definitionally equal *)
Lemma from_jmr {A} {a b : A} : jmeq a b -> a ~ b.
Proof. apply (from_jm obseq_refl). Qed.

(* Constructing an equality between two pairs *)
Lemma pair_cong {A B} (p q : ∑ x : A, B x) (e1 : π1 p ~ π1 q) :
  ap B e1 # π2 p ~ π2 q -> p ~ q.
Proof.
  destruct p,q; cbn in *.
  induction e1; cbn; intros e; induction e; reflexivity.
Qed.

(* For debugging purpose *)
Axiom todo@{s|u|} : forall {A : Type@{s|u}}, A.

Section Test.
  Universe u.
  Context (A :Type@{u}) (B : A -> Type@{u})
    (P : nat -> Type@{u})
  (C : forall (n : nat) (p : P n) (a : A), B a -> Type@{u}).

Definition T a := ∑ b : B a, forall n p, C n p a b.

Lemma Text {a1 a2 : A} (ea : a1 ~ a2) (t1 : T a1) (t2 : T a2) :
  jmeq (π1 t1) (π1 t2) ->
  (forall n p, jmeq (π2 t1 n p) (π2 t2 n p)) ->
  ap T ea # t1 ~ t2.
Proof.
  intros h1 h2.
  unshelve eapply pair_cong.
  - cbn; apply from_jmr, jm_cast_left, h1.
  - apply funext; intros n.
    apply funext; intros pn.
    apply from_jmr, jm_cast_left.
    (* BUG: If this line is commented, then there is an anomaly at Qed *)
    set (y := cast _ _ _ n); change y with n; clear y.
    (* apply todo. Qed. *) (* works *)
    cbn. (* The culprit seems to be this cbn that seems needed for the following apply to work *)
    apply jm_cast_left, h2.
Qed.
(* Error: *)
(* Anomaly *)
(* "File "kernel/cClosure.ml", line 583, characters 21-27: Assertion failed." *)
(* Please report at http://coq.inria.fr/bugs/. *)

End Test.


(* Further tests of reduction (now working) *)

Lemma castπ1@{a b ?}
  {A A' : Type@{a}}
  {B : A -> Type@{b}} {B' : A' -> Type@{b}}
  (e : (∑(a : A), B a) ~ ∑(a : A'), B' a)
  (h : ∑ (a : A), B a) :
  π1 (e # h) ~ obseq_pair_0@{a a b b max(a,b)} A A' B B' e #  π1 h.
Proof. reflexivity. Qed.


Lemma hcastπ1@{a b ?}
  {A A' : Type@{a}}
  {B : A -> Type@{b}} {B' : A' -> Type@{b}}
  (e : (∑(a : A), B a) ~ ∑(a : A'), B' a)
  (h : ∑ (a : A), B a) :
  jmeq (π1 (e # h)) (obseq_pair_0@{a a b b max(a,b)} A A' B B' e #  π1 h).
Proof. reflexivity. Qed.

Lemma hcastπ1'@{a b ?}
  {A A' : Type@{a}}
  {B : A -> Type@{b}} {B' : A' -> Type@{b}}
  (e : (∑(a : A), B a) ~ ∑(a : A'), B' a)
  (h : ∑ (a : A), B a) :
  jmeq (π1 (e # h)) (π1 h).
Proof. cbn; eapply jm_cast_left. reflexivity. Qed.


Lemma castπ2
  {A A' : Type}
  {B : A -> Type} {B' : A' -> Type}
  (e : (∑(a : A), B a) ~ ∑(a : A'), B' a)
  (h : ∑ (a : A), B a) :
  π2 (e # h) ~ obseq_pair_1' A A' B B' e h  #  π2 h.
Proof.
  progress cbn. reflexivity.
Qed.

Lemma hcastπ2
  {A A' : Type}
  {B : A -> Type} {B' : A' -> Type}
  (e : (∑(a : A), B a) ~ ∑(a : A'), B' a)
  (h : ∑ (a : A), B a) :
  jmeq (π2 (e # h)) (obseq_pair_1' A A' B B' e h  #  π2 h).
Proof.
  progress cbn. reflexivity.
Qed.
