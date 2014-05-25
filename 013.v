Inductive pos : Set :=
  | SO : pos
  | S : pos -> pos.

Fixpoint plus(n m:pos) : pos :=
  match n with
  | SO => S m
  | S p => S (plus p m)
  end.

Infix "+" := plus.

Theorem plus_assoc : forall n m p, n + (m + p) = (n + m) + p.
Proof.
  intros.
  elim n.
  simpl.
  reflexivity.
  simpl.
  intros.
  apply f_equal.
  exact H.
Qed.
