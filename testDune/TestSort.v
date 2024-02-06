Set Universe Polymorphism.
Set Primitive Projections.

Record Sum@{q |a b|} (A : Type@{q|a}) (B : A -> Type@{q|b}) : Type@{q | max(a,b)} :=
  pair { fst : A ; snd : B fst }.

(* Inductive Id@{q|a|} {A : Type@{q|a}} (x : A) : A -> Type@{q|a} := refl : Id x x. *)
Inductive Id@{a|} {A : Type@{a}} (x : A) : A -> Type@{a} := refl : Id x x.
Notation "x ≡ y" := (Id x y) (at level 65).



Record catop := { 
  obj :> Set ; 
  hom :> obj -> obj -> Set ; 
  comp : forall {x y z : obj} (f : hom x y) (g : hom y z), hom x z ;
  id : forall x, hom x x
}.

Module Nat.
  Inductive le : nat -> nat -> Prop := | le0 n : le 0 n | leS {n m} : le n m -> le (S n) (S m).
  Lemma trans {n m p} : le n m -> le m p -> le n p.
    induction 1 in p |- *.
    1: constructor.
    intros h; inversion h; subst; constructor; eauto.
  Qed.

  Lemma refl n : le n n.
  Proof. induction n; constructor; eauto. Qed.

  Definition inv_stmt n m : le n m -> Prop :=
    match n as n return le n m -> Prop with
    | 0 => fun h => h = le0 _
    | S n =>
      match m with
      | 0 => fun _ => False
      | S m => fun h => exists h' : le n m, h = leS h'
      end
    end.

  Lemma inversion {n m}  (h : le n m) : inv_stmt n m h.
  Proof.
    refine (match h as h in le n m return inv_stmt n m h with | le0 n => _ | leS h => _ end).
    all: cbn; try eexists; reflexivity.
  Qed.

  Lemma proof_irr {n m} (h1 h2 : le n m) : h1 = h2.
  Proof.
    induction n in m, h1, h2 |- *; 
    pose proof (inversion h1) as invh1; 
    pose proof (inversion h2) as invh2; cbn in *.
    1: subst; reflexivity.
    destruct m.
    1: inversion invh1.
    destruct invh1, invh2; subst; f_equal; eauto.
  Qed.
End Nat.

Definition natCat : catop :=  
  {| obj := nat ; hom n m := Nat.le n m ; comp := @Nat.trans ; id := Nat.refl |}.

Definition cast {A B : Set} (e : A = B) : A -> B :=
  match e with eq_refl => fun x => x end.

Sort psh.

Definition Psh@{u} := Type@{psh|u}.
Definition Psh'@{u} := Type@{psh|u+1}.
(* Symbol psh@{u} : Psh'@{u}. (* Psh@{u+1} *)
Symbol yon : natCat.(obj) -> Psh@{Set}. *)

Symbol on@{u} : Psh@{u} -> natCat.(obj) -> Type@{u}.
Symbol act@{u} : forall (X : Psh@{u}) {n m}, hom natCat n m -> on X m -> on X n.

Record pshf_op_ext@{u} := { 
  on_ext : natCat -> Type@{u} ; 
  act_ext : forall {n m}, hom natCat n m -> on_ext m -> on_ext n }.
  
Symbol from_ext@{u} : pshf_op_ext@{u} -> Psh@{u}.

Rewrite Rule on_from_ext := @{u} |- on@{u} (from_ext ?P) ==>  ?P.(on_ext).
Rewrite Rule act_from_ext := @{u} |- @act@{u} (from_ext ?P) ==> ?P.(@act_ext).

Definition yon_ext (m : natCat) := {| 
  on_ext := fun n => hom natCat n m ;
  act_ext := fun n m f g => comp natCat f g |}.

Notation yon n := (from_ext (yon_ext n)).


Record natTrans@{u} (X Y : Psh@{u}) :=
  { map :> forall n, on X n -> on Y n ;
    natural : forall {n m} (f : hom natCat n m) (xm : on X m),
      act Y f (map m xm) ≡ map n (act X f xm)
  }.

Record prod@{q|a b|} (A : Type@{q|a}) (B : Type@{q|b}) : Type@{q|max(a,b)} := mk_pair {π1 : A ; π2 : B}.
Notation "X × Y" := (prod X Y) (at level 70).


(* Hack around limitations of pattern matching on -> in rewrite rules *)
Symbol arr@{a b} : forall (A : Psh@{a}) (B : Psh@{b}), Type@{psh|max(a,b)}.
Symbol to_arr@{a b}: forall {A : Psh@{a}} {B : Psh@{b}}, (A -> B) -> arr A B. 
Symbol from_arr@{a b}: forall {A : Psh@{a}} {B : Psh@{b}}, arr A B -> (A -> B). 
Rewrite Rule from_to_arr := @{a b} |- from_arr (@to_arr@{a b} ?A ?B ?f) ==> ?f.
Rewrite Rule to_from_arr := @{a b} |- to_arr (@from_arr@{a b} ?A ?B ?f) ==> ?f.

Definition psh_prod@{a b} := prod@{psh|a b}. 

Rewrite Rule on_arr := @{u1 u2 v} |- on@{v} (arr@{u1 u2} ?X ?Y) ?n ==> natTrans@{v} (psh_prod@{u1 Set} ?X (yon ?n)) ?Y.


Record pb {X Y Z} {f : X -> Z} {g : Y -> Z} := { pbl : X ; pbr : Y ; pbeq : f pbl ≡ g pbr }.
Arguments pb : clear implicits.
Arguments pb {_ _ _}.

Definition pb_universal_exists {X Y Z} (f : X -> Z) (g : Y -> Z) {U} (hf : U -> X) (hg : U -> Y)
(heq : forall u, f (hf u) ≡ g (hg u)) : U -> pb f g :=
  fun u => {| pbl := hf u ; pbr := hg u ; pbeq := heq u |}.

Definition pb_map 
  {X1 Y1 Z1} (f1 : X1 -> Z1) (g1 : Y1 -> Z1)
  {X2 Y2 Z2} (f2 : X2 -> Z2) (g2 : Y2 -> Z2)
  (hX : X1 -> X2)
  (hY : Y1 -> Y2)
  (hZ : Z1 -> Z2)
  (hf : forall x1, hZ (f1 x1) ≡ f2 (hX x1))
  (hg : forall y1, hZ (g1 y1) ≡ g2 (hY y1))
  : pb f1 g1 -> pb f2 g2.
Proof.
  refine (pb_universal_exists f2 g2 (fun pb1 => hX pb1.(pbl)) (fun pb1 => hY pb1.(pbr)) _).
  intros pb1; now rewrite <- hf, <- hg, pb1.(pbeq).
Defined.

Definition pb_ext (X Y Z : Psh) (f : natTrans X Z) (g : natTrans Y Z) : pshf_op_ext :=
  {|
    on_ext n := pb (f n) (g n) ;
    act_ext n m h := pb_map (f m) (g m) (f n) (g n) (act X h) (act Y h) (act Z h) (natural _ _ _ _) (natural _ _ _ _);
  |}.

Notation pb_psh f g := (from_ext (pb_ext _ _ _ f g)).

Definition yon_map_ext@{u} {n m} (f : hom natCat n m) : natTrans@{u} (yon n) (yon m).
  unshelve econstructor.
  - intros ? h; refine (comp natCat h f). 
  - cbn; intros; erewrite Nat.proof_irr; reflexivity.
Qed.

Definition pshf_ext@{u v} : pshf_op_ext@{v}.
Proof.
  refine {|
    on_ext n := { X : Psh@{u} & natTrans@{u} X (yon n)} ;
    act_ext n m f xm := existT _ (pb_psh (projT2 xm) (yon_map_ext f)) _ 
  |}.
  exists (fun m => pbr); reflexivity.
Defined.

Notation psh := (from_ext pshf_ext).

Definition el (A : psh) : Psh := 

(* Hack around limitations of pattern matching on Π in rewrite rules *)
Symbol pi@{a b b'} : forall (A : Psh@{a}) (B : A -> from_ext pshf_ext@{b b'}), Type@{psh|max(a,b)}.
Symbol to_pi@{a b}: forall {A : Psh@{a}} {B : Psh@{b}}, (forall x: A, B x) -> pi A B. 
Symbol from_pi@{a b}: forall {A : Psh@{a}} {B : Psh@{b}}, pi A B -> (A -> B). 
Rewrite Rule from_to_pi := @{a b} |- from_pi (@to_pi@{a b} ?A ?B ?f) ==> ?f.
Rewrite Rule to_from_pi := @{a b} |- to_pi (@from_pi@{a b} ?A ?B ?f) ==> ?f.

Record dPsh@{u} {X : Psh@{u}} := mkDPsh { total :> Psh@{u} ; display : natTrans total X }.
Arguments dPsh : clear implicits.

(* Definition ond@{u} {X : Psh@{u}} (Y : dPsh X) (n : natCat) (x : on X n) :=
  { y : on Y n & display Y n y = x }. *)

(* Definition X@{u} n := dPsh@{u+1} (yon n). Type@{u+2}. *)

Rewrite Rule on_psh := @{u v | u < v } |- on@{v} psh@{u} ?n ==> (dPsh@{u} (yon ?n) : Type@{v}).
Rewrite Rule on_yon := on (yon ?n) ?m ==> hom natCat ?m ?n.
Rewrite Rule act_yon := @act (yon ?n) ?k ?l ?f ?h ==> @comp natCat ?k ?l ?n ?f ?h.

Module Type CatSIG.
  Sort q.
  Monomorphic Universe u.
  Definition Tq@{v} := Type@{q|v}.
  Axiom Obj : Type@{q|u}.
  Axiom Hom : Obj -> Obj -> Type@{q|u}.
  Axiom id : forall (A : Obj), Hom A A.
  Axiom comp : forall (A B C : Obj), Hom A B -> Hom B C -> Hom A C.
End CatSIG.

Module Presheaf(C : CatSIG).
  Sort p.
  Definition Ps@{u} := Type@{p|u}.
  Set Printing Universes.
  Symbol on@{u} : Ps@{u} -> C.Obj -> C.Tq@{u}.


Definition pb (X1 X2 : Psh@{u}) (α : natTrans X1 X2) (Y : dPsh X2) : dPsh X1 :=
  Sum X1 (fun x1 => Sum Y (fun y => ))

Record psh@{s|u v|} {C : catop} := {
    Idx := Type@{s|u} ;

    on : Idx -> C -> Set ;
    act : forall (X : Idx) {x y : C} (f : hom C x y), on X y -> on X x ;
    act_id : forall (X : Idx) (x : C) (a : on X x), act X (id C x) a = a ;
    act_comp : forall (X : Idx) {x y z: C} (f : hom C x y) (g : hom C y z) (a : on X z), 
      act X (comp C f g) a = act X f (act X g a) ;

    discr : Set ->  Idx ;
    on_discr : forall A x, A = on (discr A) x;
    act_discr : forall (A : Set) {x y} (f : hom C x y) (a : A),
      act (discr A) f (cast (on_discr A y) a) = cast (on_discr A x) a ;

    yon : C -> Idx ;
    on_yon : forall x y, hom C x y = on (yon y) x ;
    act_yon : forall {x y z} (f : hom C x y) (g : hom C y z),
      act (yon z) f (cast (on_yon y z) g) = cast (on_yon x z) (comp C f g) ;
}.

Arguments psh : clear implicits.

Set Allow Rewrite Rules.


Symbol Trees : psh natCat.

Inductive terminal : Trees.(Idx) := uniq : terminal.

Set Printing Universes.
Check Trees.(Idx).

Definition id'@{u} (A : Type@{u}) : A -> A := fun x => x.

Check id' Trees.(Idx).

Rewrite Rule on_discr_rw := Trees.(on) (Trees.(discr) ?A) ?x ==> ?A.
Rewrite Rule act_discr_rw := Trees.(act) (Trees.(discr) ?A) ?f ?x ==> ?x.

Record nat_trans (A : Trees.(Idx)) (B : A -> Tree.(Idx)) (n : natCat) :=
  {| 
    map :> forall {p} (α : hom natCat p n) (a : Trees.(on) A p), Trees.(on) (B a) p ;
    natural : forall {p q} (α : hom natCat p n) (β : hom natCat q p),
      Trees.(act) (B a) β (map α a) = map (comp natCat β α) a
  |}

Rewrite Rule on_forall_rw  := Trees.(on) (forall x : ?A, ?B) ?x ==> ()





Set Definitional UIP.
Inductive Eq {A} (x : A) : A -> SProp := refl : Eq x x.
Inductive Box@{u} (P : SProp) : Type@{u} := box : P -> Box P.
