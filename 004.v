Theorem DeMorgan1 : forall P Q : Prop, ~P \/ ~Q -> ~(P /\ Q).
Proof.
  intros.
  destruct H.
  contradict H.
  apply H.
  contradict H.
  apply H.
Qed.

Theorem DeMorgan2 : forall P Q : Prop, ~P /\ ~Q -> ~(P \/ Q).
Proof.
  intros.
  destruct H.
  contradict H.
  destruct H.
  assumption.
  contradict H0.
  assumption.
Qed.

Theorem DeMorgan3 : forall P Q : Prop, ~(P \/ Q) -> ~P /\ ~Q.
Proof.
  intros.
  split.
  contradict H.
  left.
  assumption.
  contradict H.
  right.
  assumption.
Qed.
