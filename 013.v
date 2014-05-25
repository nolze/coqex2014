Inductive pos : Set :=
  | SO : pos
  | S : pos -> pos.

Fixpoint plus(n m:pos) : pos :=
  match n with
  | SO => S m
  | S p => S (p + m)
  end
where "n + m" := (plus n m).

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
