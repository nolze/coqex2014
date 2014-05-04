Require Import Arith.

Definition Nat : Type :=
  forall A : Type, (A -> A) -> (A -> A).

Definition NatPlus(n m : Nat) : Nat :=
  fun A f x => n A f (m A f x).

Definition nat2Nat : nat -> Nat := nat_iter.

Definition Nat2nat(n : Nat) : nat := n _ S O.

Lemma NatPlus_plus :
  forall n m, Nat2nat (NatPlus (nat2Nat n) (nat2Nat m)) = n + m.
Proof.
  intros.
  unfold Nat2nat.
  unfold NatPlus.
  unfold nat2Nat.
  rewrite <- nat_iter_plus.
  induction n.
  simpl.
  induction m.
  simpl.
  reflexivity.
  rewrite <- IHm.
  simpl.
  apply f_equal.
  rewrite IHm.
  rewrite IHm.
  reflexivity.
  simpl.
  apply f_equal.
  exact IHn.
Qed.
