(* 
    This file covers definitions and proofs 
    regarding boolean values
*)

Inductive bool : Type :=
| true
| false.

Definition eqb (b_1 b_2 : bool) : bool :=
    match b_1 with
    | true => match b_2 with
        | true => true
        | false => false
        end
    | false => match b_2 with
        | true => false
        | false => true
        end
    end.

Example eqb_f_f: eqb false false = true.
Proof. reflexivity. Qed.
Example eqb_t_f: eqb true false = false.
Proof. reflexivity. Qed.
Example eqb_f_t: eqb false true = false.
Proof. reflexivity. Qed.
Example eqb_t_t: eqb true true = true.
Proof. reflexivity. Qed.

Definition notb (b : bool) : bool :=
    match b with 
    | true => false
    | false => true
    end.

Example notb_f: notb false = true.
Proof. reflexivity. Qed.
Example notb_t: notb true = false.
Proof. reflexivity. Qed.

Definition andb (b_1 b_2 : bool) : bool :=
    match b_1 with
    | true => match b_2 with 
        | true => true
        | false => false
        end
    | false => false
    end.

Notation "x && y" := (andb x y).

Example andb_f_f: andb false false = false.
Proof. reflexivity. Qed.
Example andb_t_f: andb true false = false.
Proof. reflexivity. Qed.
Example andb_f_t: andb false true = false.
Proof. reflexivity. Qed.
Example andb_t_t: andb true true = true.
Proof. reflexivity. Qed.

Definition orb (b_1 b_2 : bool) : bool := 
    match b_1 with 
    | true => true
    | false => b_2
    end.

Example orb_f_f: orb false false = false.
Proof. reflexivity. Qed.
Example orb_t_f: orb true false = true.
Proof. reflexivity. Qed.
Example orb_f_t: orb false true = true.
Proof. reflexivity. Qed.
Example orb_t_t: orb true true = true.
Proof. reflexivity. Qed.

Notation "x || y" := (orb x y).

Definition xorb (b_1 b_2 : bool) : bool :=
    match b_1 with 
    | true => match b_2 with
        | true => false
        | false => true
        end
    | false => match b_2 with
        | true => true
        | false => false
        end
    end.

Example xorb_f_f: xorb false false = false.
Proof. reflexivity. Qed.
Example xorb_t_f: xorb true false = true.
Proof. reflexivity. Qed.
Example xorb_f_t: xorb false true = true.
Proof. reflexivity. Qed.
Example xorb_t_t: xorb true true = false.
Proof. reflexivity. Qed.

Theorem A_implies_A : forall A : Prop, 
    A -> A.
Proof.
    intros A. intros H. exact H.
Qed.
