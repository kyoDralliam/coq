
Set Universe Polymorphism.


Module Foo.

  Sort q1 q2.
  Fail Check  fun (A : Type@{q1|Set}) => A : Type@{q2|Set}.

  Fail Sorts q q.
End Foo.


Module Exc.
  Sort exc.
  Definition Exc@{u} := Type@{exc|u}.
  Axiom raise@{u} : forall (A : Exc@{u}), A.

  Inductive boolE : Exc := trueE | falseE.
End Exc.


Module Pred.

  Sort pred.

  Definition Pred@{u} := Type@{pred|u}.

  Axiom P: Pred@{Set}.
End Pred.

Import Exc.
Import Pred.

Set Printing Universes.

Fail Check fun (A : Exc) => (A : Pred).

Check trueE.
Check P.
Check boolE.


Module Type CAT.
  Sort q.
  Definition Q@{u} := Type@{q|u}.
  Axiom Obj : Q.
  Axiom Hom : forall (x y : Obj), Q.
  Axiom id : forall (o : Obj), Hom o o.
  Axiom comp : forall {x y z : Obj} (f : Hom x y) (g : Hom y z), Hom x z.
End CAT.

Module Functor(C : CAT).
  Sort psh.
  Definition Psh@{u} := Type@{psh|u}.
  Axiom on@{u} : forall (X : Psh@{u}) (c : C.Obj), Type@{C.q|u}.
End Functor.