Require Import ZArith.
Require Import List.
Require Extraction.

Set Implicit Arguments.

(* ================================================================================== *)
(* ====================================EXERCÍCIO 1=================================== *)
(* ================================================================================== *)

(*1. Apresente uma especificação forte adequada a cada uma das funções abaixo indicadas.
     Faça a prova desses teoremas (especificação) e, por fim, proceda à extração do respectivo programa Haskell.*)

  (*a) Uma função que, dado um número natural n e um valor x, constroi uma lista de tamanho n cujos elementos são todos iguais a x.*)
  Inductive CreateNList (A: Type) : nat -> A -> (list A) -> Prop :=
    | CNLzero : forall (x : A), CreateNList 0%nat x nil
    | CNLsucc : forall (n: nat) (x: A) (l: list A), CreateNList n x l -> CreateNList (S n) x (x::l).

  Theorem ex1a : forall (A: Type) (n: nat) (x: A), { l: list A | CreateNList n x l }.
  Proof.
    intros.
    induction n.
    - exists nil. apply CNLzero.
    - elim IHn. intros. exists (x::x0). apply CNLsucc. apply p.
  Qed.

  Extraction Language Haskell.
  Recursive Extraction ex1a.
  Extraction Inline nat_rect.
  Extraction Inline sig_rect.
  Recursive Extraction ex1a.

  Extraction "ex1a" ex1a.

  (*b) Uma função que recebe uma lista de pares de números naturais, e produz a lista com as somas das partes constituintes de cada par da lista.*)
  Inductive PairList : (list (nat*nat)) -> (list nat) -> Prop :=
    | PLnil  : PairList nil nil
    | PLcons : forall (p: (nat*nat)) (l1: list (nat*nat)) (l2: list nat), PairList l1 l2 -> PairList (p::l1) ((fst p + snd p)::l2).

  Theorem ex1b : forall (l1: list (nat*nat)), { l2: list nat | PairList l1 l2 }.
  Proof.
    intros.
    induction l1.
    - exists nil. apply PLnil.
    - elim IHl1. intros. exists ((fst a+snd a)::x). apply PLcons. apply p.
  Qed.

  Extraction Language Haskell.
  Recursive Extraction ex1b.
  Extraction Inline list_rect.
  Extraction Inline list_rec.
  Extraction Inline sig_rec.
  Recursive Extraction ex1b.

  Extraction "ex1b" ex1b.

(* ================================================================================== *)
(* ====================================EXERCÍCIO 2=================================== *)
(* ================================================================================== *)

(*2. Recorde a função count que conta o número de ocorrências de um inteiro numa lista de inteiros.*)
Fixpoint count (z: Z) (l: list Z) {struct l} : nat :=
  match l with
    | nil => 0%nat
    | (z' :: l') => if (Z.eq_dec z z')
                    then S (count z l')
                    else count z l'
  end.

  (*a) Prove a seguinte propriedade*)
  Theorem ex2a : forall (x: Z) (a: Z) (l: list Z), x <> a -> count x (a :: l) = count x l.
  Proof.
    intros.
    simpl.
    elim (Z.eq_dec x a).
      - easy.
      - intros. reflexivity.
  Qed.

  (*b) Defina uma relação indutiva que descreva a relação entre o input e o output para a função count, ou seja, a sua especificação.*)
  Inductive CountRelation : Z -> (list Z) -> nat -> Prop :=
    | CRnil     : forall (x: Z), CountRelation x nil 0%nat
    | CRheadEq  : forall (x: Z) (l: list Z) (n: nat), CountRelation x l n -> CountRelation x (x::l) (S n)
    | CRheadDif : forall (x y: Z) (l: list Z) (n: nat), (x <> y /\ CountRelation x l n) -> CountRelation x (y::l) n.


  (*c) Prove que a função dada acima satisfaz a especiificação apresentada na alínea anterior.*)
  Theorem ex2c : forall (x: Z) (l: list Z), CountRelation x l (count x l).
  Proof.
    intros.
    induction l.
    - simpl. apply CRnil.
    - simpl. elim (Z.eq_dec x a).
      + intros. replace a with x. apply CRheadEq. apply IHl.
      + intros. apply CRheadDif. split.
        * apply b.
        * apply IHl.
  Qed.