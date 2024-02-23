
Sort comp.
Definition Comp := Type@{comp|Set}.


Inductive natC : Comp := ZC : natC | SC : natC -> natC.

Fail Fixpoint natC_rect (P : natC -> Type) (hZ : P ZC) (hS : forall n, P n -> P (SC n)) n {struct n} : P n :=
  match n with
  | ZC => hZ
  | SC n => hS n (natC_rect P hZ hS n)
  end.

Fixpoint natC_rect (P : natC -> Comp) (hZ : P ZC) (hS : forall n, P n -> P (SC n)) n {struct n} : P n :=
  match n with
  | ZC => hZ
  | SC n => hS n (natC_rect P hZ hS n)
  end.

Fixpoint nat_recC (P : nat -> Comp) (hZ : P 0) (hS : forall n, P n -> P (S n)) n {struct n} : P n :=
  match n with
  | 0 => hZ
  | S n => hS n (nat_recC P hZ hS n)
  end.
