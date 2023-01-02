(*
    This file covers definitions and
    proofs regarding multisets.
*)

From Collections Require Export Lists.

Variable A : Type.

(*
    TA Definition 3.1.1
*)
Definition multiset := list.

Notation "{ }" := empty.
Notation "{ x ; .. ; y }" := (cons x .. (cons y empty) ..).

(*
    TA Axiom 3.1

    Sets are objects
*)
Theorem sets_are_objects : forall l : multiset A, exists m : multiset (multiset A),
    contains l m.
Proof.
    intros l. exists {l}. simpl.
    left. reflexivity.
Qed.
