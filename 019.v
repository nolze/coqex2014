Parameter A : Set.
Definition Eq : A -> A -> Prop :=
  fun a b => forall f : (A -> Prop), f a -> f b.

Lemma Eq_eq : forall x y, Eq x y <-> x = y.
Proof.
  intros.
  split.
  - intros.
    apply H.
    reflexivity.
  - intros.
    unfold Eq.
    intros.
    rewrite <- H.
    apply H0.
Qed.
