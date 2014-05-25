Require Import Coq.Logic.Classical.

Lemma ABC_iff_iff :
    forall A B C : Prop, ((A <-> B) <-> C) <-> (A <-> (B <-> C)).
Proof.
  intros.
  tauto.
Qed.

Goal
  forall P Q R : Prop,
  (IF P then Q else R) ->
  exists b : bool,
  (if b then Q else R).
Proof.
  intros P Q R HIF.
  case HIF.
  - intros.
    exists true.
    apply H.
  - intros.
    exists false.
    apply H.
Qed.

Require Import Coq.Logic.ClassicalDescription.

Goal
  forall P Q R : nat -> Prop,
  (forall n, IF P n then Q n else R n) ->
  exists f : nat -> bool,
  (forall n, if f n then Q n else R n).
Proof.
  intros.
  exists (fun (x : nat) => (if excluded_middle_informative (P x) then true else false)).
  intros.
  case (H n).
  destruct excluded_middle_informative.
  - intros H0.
    apply H0.
  - intros.
    exfalso.
    apply n0.
    apply H0.
  - intro.
    destruct excluded_middle_informative.
    exfalso.
    apply H0.
    apply p.
    apply H0.
Qed.
