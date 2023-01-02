(*
    This file covers definitions and
    proofs regarding pair and list
    structures.
*)

Variable A : Type.

Inductive pair (A : Type) : Type :=
    | pairc (n_1 n_2 : A).
Arguments pairc {A} n_1 n_2.

Definition first {A : Type} (p : pair A) : A :=
    match p with
    | pairc x y => x
    end.

Definition second {A : Type} (p : pair A) : A :=
    match p with
    | pairc x y => y
    end.

Notation "( x , y )" := (pairc x y).

Definition swap_pair {A : Type} (p : pair A) : pair A :=
    match p with
    | (x, y) => (y, x)
    end.

Theorem surjective_pairing : forall (p : pair A),
    p = (first p, second p).
Proof.
    intros p. destruct p as [n m].
    simpl. reflexivity.
Qed.

Theorem second_first_is_swap : forall (p : pair A),
    (second p, first p) = swap_pair p.
Proof.
    intros p. destruct p as [n m].
    simpl. reflexivity.
Qed.

Theorem first_swap_is_second : forall (p : pair A),
    first (swap_pair p) = second p.
Proof.
    intros p. destruct p as [n m].
    simpl. reflexivity.
Qed.

Inductive list (A : Type) : Type := 
    | empty : list A 
    | cons (n : A) (l : list A).
Arguments empty {A}.
Arguments cons {A} n l.

Notation "x :: l" := (cons x l)
    (at level 60, right associativity).

Notation "[ ]" := empty.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y empty) ..).

Fixpoint length {A : Type} (l : list A) : nat :=
  match l with
    | empty => 0
    | h :: t => 1 + (length t)
  end.

Fixpoint append {A : Type} (l1 l2 : list A) :=
    match l1 with
    | empty => l2
    | h :: t => h :: (append t l2)
    end.

(* Notation "x ++ y" := (append x y) 
    (at level 60, right associativity). *)

Infix "++" := append (right associativity, at level 60).

Definition head {A : Type} (default : A) (l : list A) : A :=
    match l with
    | empty => default
    | h :: t => h
    end.

Definition tail {A : Type} (l : list A) : list A :=
    match l with
    | empty => empty
    | h :: t => t
    end.

Fixpoint contains {A : Type} (n : A) (l : list A) : Prop :=
    match l with
    | empty => False
    | h :: t => h = n \/ (contains n t)
    end.
