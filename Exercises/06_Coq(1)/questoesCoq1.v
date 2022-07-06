(*==================================================================*)
(*======================= Propositional Logic ======================*)
(*==================================================================*)
Section PL.

Variables A B C D: Prop.

Lemma ex11: (A -> C) /\ (B -> C) -> (A /\ B) -> C.
Proof.
  intros.
  destruct H as [H1 H2].
  apply H1.
  apply H0.
Qed.

Lemma ex12: ~A \/ ~B -> ~(A /\ B).
Proof.
  intros.
  intro.
  destruct H0 as [H1 H2].
  elim H.
    - intro. apply H0. apply H1.
    - intro. apply H0. apply H2.
Qed.

Lemma ex13: (A -> (B \/ C)) /\ (B -> D) /\ (C -> D) -> (A -> D).
Proof.
  intros.
  destruct H as [H1 H2].
  destruct H2 as [H3 H4].
  elim H1.
    - apply H3.
    - apply H4.
    - apply H0.
Qed.

Lemma ex14: (A /\ B) -> ~(~A \/ ~B).
Proof.
  intros.
  intro.
  destruct H as [H1 H2].
  elim H0.
    - intro. apply H. apply H1.
    - intro. apply H. apply H2.
Qed.

End PL.

(*==================================================================*)
(*======================== First-Order Logic =======================*)
(*==================================================================*)
Section FOL.

Variable X: Set.
Variable t: X.
Variable P Q R: X -> Prop.

Lemma ex21: (forall x, (P x) -> (Q x)) -> (forall y, ~(Q y)) -> (forall x, ~(P x)).
Proof.
  intros.
  intro.
  apply (H0 x).
  apply H.
  exact H1.
Qed.

Lemma ex22: (forall x, (P x) \/ (Q x)) -> (exists y, ~(Q y)) -> (forall x, (R x) -> ~(P x)) -> (exists x, ~(R x)).
Proof.
  intros.
  destruct H0.
  exists x.
  intro.
  destruct (H x).
  - apply (H1 x). exact H2. exact H3.
  - apply H0. exact H3.
Qed.

End FOL.

(*==================================================================*)
(*========================= Classical Logic ========================*)
(*==================================================================*)
Section CL.

Variable A B: Prop.
Variable X: Set.
Variable t: X.
Variable P: X -> Prop.

Axiom pme: forall Q: Prop, Q \/ ~Q.
Axiom double_neg_law : forall A:Prop, ~~A -> A.

Lemma ex31: (~A -> B) -> (~B -> A).
Proof.
  intros.
  elim (pme A).
  trivial.
  intros.
  apply H in H1.
  contradiction.
Qed.

Lemma ex32: ~(exists x: X, ~(P x)) -> (forall x: X, P x).
Proof.
  intros.
  elim (pme (P x)).
  trivial.
  intro.
  absurd (exists x0, ~(P x0)).
  trivial.
  exists x.
  assumption.
Qed.

Lemma ex33: ~(forall x: X, ~(P x)) -> (exists x: X, P x).
Proof.
  intros.
  elim (pme (exists x, P x)).
  intro.
  assumption.
  intro H1.
  elim H.
  red.
  intros.
  apply H1.
  exists x.
  apply H0.
Qed.

End CL.