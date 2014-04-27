Theorem Disjunctive_syllogism : forall P Q : Prop, (P \/ Q) -> ~P -> Q.
Proof.
  intros.
  destruct H.
  contradict H0.
  assumption.
  assumption.
Qed.
