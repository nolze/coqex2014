Require Import Lists.List.

Fixpoint sum (xs: list nat) : nat :=
  match xs with
    | nil => 0
    | x :: xs => x + sum xs
  end.

Lemma lt_Snm_nm : forall (n m : nat), S n < m -> n < m.
  intros.
  apply (Lt.lt_trans n (S n) m).
  apply Lt.lt_n_Sn.
  assumption.
Qed.

Theorem Pigeon_Hole_Principle :
  forall (xs : list nat), length xs < sum xs -> (exists x, 1<x /\ In x xs).
Proof.
  intros.
  induction xs.
  exfalso.
  simpl in H.
  apply Lt.lt_irrefl in H.
  exact H.

  destruct a.
  simpl in H.
  apply lt_Snm_nm in H.
  apply IHxs in H.
  destruct H.
  exists x.
  constructor.
  apply H.
  simpl. right. apply H.

  destruct a.
  simpl in H.
  apply Lt.lt_S_n in H.
  apply IHxs in H.
  destruct H.
  exists x.
  constructor.
  apply H.
  simpl. right. apply H.

  exists (S (S a)).
  constructor.
  simpl in H.
  apply Lt.lt_n_S.
  apply Lt.lt_0_Sn.
  simpl. left. reflexivity.
Qed.
