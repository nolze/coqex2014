Theorem NotNot_Lem : forall P : Prop, ~ ~(P \/ ~P).
Proof.
  intros.
  intro.
  apply H.
  right.
  intro.
  apply H.
  left.
  assumption.
Qed.
