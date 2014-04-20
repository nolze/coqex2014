Theorem Modus_tollens : forall P Q : Prop, ~Q /\ (P -> Q) -> ~P.
Proof.
  intros.
  destruct H.
  contradict H.
  apply H0.
  assumption.
Qed.
