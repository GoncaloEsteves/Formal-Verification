Require Import List.
Require Import ZArith.

Set Implicit Arguments.

Inductive In (A: Type) (y: A) : list A -> Prop :=
  | InHead : forall (xs: list A), In y (cons y xs)
  | InTail : forall (x: A) (xs: list A), In y xs -> In y (cons x xs).

Inductive Prefix (A: Type) : list A -> list A -> Prop :=
  | PreNil  : forall (l: list A), Prefix nil l
  | PreCons : forall (x: A) (l1 l2: list A), Prefix l1 l2 -> Prefix (x::l1) (x::l2).

Inductive SubList (A: Type) : list A -> list A -> Prop :=
  | SLnil   : forall (l: list A), SubList nil l
  | SLcons1 : forall (x: A) (l1 l2: list A), SubList l1 l2 -> SubList (x::l1) (x::l2)
  | SLcons2 : forall (x: A) (l1 l2: list A), SubList l1 l2 -> SubList l1 (x::l2).


(*Exercicio 1 - Prove as seguintes propriedades*)

Theorem ex1a: SubList (5::3::nil) (5::7::3::4::nil) .
Proof.
  apply SLcons1.
  apply SLcons2.
  apply SLcons1.
  apply SLnil.
Qed.

Theorem ex1b: forall (A: Type) (l: list A), SubList l l .
Proof.
  induction l.
    - apply SLnil.
    - apply SLcons1. apply IHl.
Qed.

Theorem ex1c: forall (A B: Type) (f: A->B) (l1 l2: list A), SubList l1 l2 -> SubList (map f l1) (map f l2) .
Proof.
  intros.
  induction H.
    - simpl. apply SLnil.
    - simpl. apply SLcons1. apply IHSubList.
    - simpl. apply SLcons2. apply IHSubList.
Qed.

Theorem aux1: forall (A: Type) (x a: A) (l: list A), In x (a :: l) <-> x = a \/ In x l .
Proof.
  red.
  split.
    - intros. inversion H.
      + left. trivial.
      + right. apply H1.
    - intros. destruct H.
      + rewrite H. apply InHead.
      + apply InTail. apply H.
Qed.

Theorem aux2: forall (A: Type) (x: A) (l1 l2: list A), x :: l1 = x :: l2 <-> l1 = l2 .
Proof.
  red.
  split.
    - intros. inversion H. trivial.
    - intros. inversion H. trivial.
Qed.

Theorem ex1d: forall (A: Type) (x: A) (l: list A), In x l -> exists l1, exists l2, l = l1 ++ (x::l2) .
Proof.
  intros.
  induction l.
  inversion H.
  apply aux1 in H.
  destruct H.
    - rewrite H. exists nil. exists l. rewrite app_nil_l. trivial.
    - apply IHl in H. destruct H as [l1 H]. destruct H as [l2 H]. exists (a::l1). exists l2. simpl. apply aux2. apply H.
Qed.


(*Exercicio 2 - Defina a função recursiva drop que dado um número natural n e uma lista l, retira os n primeiros elementos de l.*)

Fixpoint drop (A: Type) (n: nat) (l: list A) : list A :=
  match n with
    | 0 => l
    | S n' => match l with
               | nil  => l
               | h::t => drop n' t
             end 
  end.

Theorem ex2a: drop 2 (5::7::3::4::nil) = 3::4::nil .
Proof.
  simpl.
  trivial.
Qed.

Theorem ex2b: forall (A:Type) (n:nat) (l:list A), SubList (drop n l) l .
Proof.
  induction n.
  - simpl. apply ex1b.
  - induction l.
    + simpl. apply SLnil.
    + simpl. apply SLcons2. apply IHn.
Qed.


(*Exercicio 3 - Defina indutivamente o predicado Sorted sobre listas de números naturais.*)

Inductive Sorted : list nat -> Prop :=
  | Snil  : Sorted nil
  | Sone  : forall (x: nat), Sorted (x::nil)
  | Scons : forall (x y: nat) (l: list nat), y<=x /\ Sorted (x::l) -> Sorted (y::x::l) .

Theorem ex3a: forall (x y: nat) (l: list nat), x<=y -> (Sorted (y::l)) -> Sorted (x::l) .
Proof.
  intros.
  induction l.
    - apply Sone.
    - apply Scons. inversion H0. subst. destruct H2 as [H1 H2]. split.
      + apply le_trans with (m := y).
        * apply H.
        * apply H1.
      + inversion H0. apply H2.
Qed.

Theorem aux3: forall (x y: nat) (l: list nat), Sorted (x::y::l) -> Sorted (x::l) .
Admitted.


Theorem ex3b: forall (x y: nat) (l: list nat), (In y l) /\ (Sorted (x::l)) -> x<=y .
Proof.
  intros.
  destruct H as [H1 H2].
  inversion H1.
  subst.
  - inversion H2. apply H0.
  - subst. induction H1. inversion H2. subst.
    + apply H1.
    + apply IHIn. apply aux3 with (y := x1). apply H2.
Qed.


(*Exercicio 4 - Prove que a relação Prefix é uma relação de ordem.*)

Theorem ex4a: forall (A: Type) (l : list A), Prefix l l .
Proof.
  induction l.
    - apply PreNil.
    - apply PreCons. apply IHl.
Qed.

Theorem ex4b: forall (A: Type) (l1 l2 l3: list A), Prefix l1 l2 /\ Prefix l2 l3 -> Prefix l1 l3 .
Admitted.

Theorem ex4c: forall (A: Type) (l1 l2: list A), Prefix l1 l2 /\ Prefix l2 l1 -> l1 = l2 .
Admitted.
