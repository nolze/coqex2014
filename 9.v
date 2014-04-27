Require Import Arith.

Goal forall n m p q : nat, (n + m) + (p + q) = (n + p) + (m + q).
Proof.
  intros.
  rewrite plus_permute_2_in_4.
  reflexivity.
Qed.

Goal forall n m : nat, (n + m) * (n + m) = n * n + m * m + 2 * n * m.
Proof.
  intros.
  simpl.
  rewrite plus_0_r.
  rewrite mult_plus_distr_l.
  rewrite mult_comm.
  rewrite mult_plus_distr_l.
  repeat rewrite mult_plus_distr_r.
  rewrite plus_assoc.
  rewrite plus_comm.
  repeat rewrite plus_assoc.
  rewrite plus_assoc_reverse.
  rewrite plus_assoc_reverse.
  rewrite plus_permute.
  repeat rewrite plus_assoc.
  reflexivity.
Qed.
