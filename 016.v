Definition tautology : forall P : Prop, P -> P
  := fun (P : Prop) => fun P => P.

Definition Modus_tollens : forall P Q : Prop, ~Q /\ (P -> Q) -> ~P
  := fun (P Q : Prop) (H : ~ Q /\ (P -> Q)) =>
  match H with
  | conj HnQ HPQ => fun (HP : P) => HnQ (HPQ HP)
  end.

Definition Disjunctive_syllogism : forall P Q : Prop, (P \/ Q) -> ~P -> Q
 := fun (P Q : Prop) (HdPQ : P \/ Q) (HnP : ~ P) =>
  match HdPQ with
  | or_introl HP =>
    match HnP HP return Q with
    end
  | or_intror HQ => HQ
  end.

Definition tautology_on_Set : forall A : Set, A -> A
  := fun (A : Set) => fun A => A.

Definition Modus_tollens_on_Set : forall A B : Set, (B -> Empty_set) * (A -> B) -> (A -> Empty_set)
  := fun (A B : Set) (H : (B -> Empty_set) * (A -> B)) (HA : A) => fst H ((snd H) HA).

Definition Disjunctive_syllogism_on_Set : forall A B : Set, (A + B) -> (A -> Empty_set) -> B
 := fun (A B : Set) (HsAB : A + B) (HnA : (A -> Empty_set)) =>
  match HsAB with
  | inl HA =>
    match HnA HA return B with
    end
  | inr HB => HB
  end.
