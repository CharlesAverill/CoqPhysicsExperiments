(* 
    This file covers definitions and 
    proofs regarding natural numbers.
    
    These definitions follow from 
    Terence Tao's 'Analysis'.

    Coq's standard library provides an
    implementation of natural numbers 
    with builtin decimal parsing. I'd 
    like to use that, so much of this 
    file is just proving that the axioms 
    are true given the definitions of 
    various sets of numbers that Coq has 
    already put in place.
*)

From Scalars Require Export Booleans.
From Collections Require Export Lists.
From Collections Require Export Multisets.

Fixpoint eqb (n m : nat) : bool :=
    match n with
    | O => match m with
        | O => true
        | _ => false
        end
    | S n' => match m with
        | O => false
        | S m' => eqb n' m'
        end
    end.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.

(* 
    TA Axiom 2.1 

    Zero is a natural number.
*)
Theorem zero_is_nat : exists n : nat,
    n = 0.
Proof. 
    now exists O.
Qed.

(* 
    TA Axiom 2.2 

    If n is a natural number, then 
    m = S(n) is also a natural number.
*)
Theorem S_n_is_nat : forall n : nat, exists m : nat,
    S(n) = m.
Proof.
    intros n. induction n as [| n' IHn' ].
    - (* n = 0 *) 
        now exists (S O).
    - (* n = S n' *)
        now exists (S (S n')).
Qed.

(* 
    TA Proposition 2.1.4
    
    3 is a natural number.
*)
Proposition nat_3 : exists n : nat,
    n = 3.
Proof.
    now exists (S (S (S O))).
Qed.

(*
    TA Axiom 2.3
    
    0 is not the successor of any 
    natural number; i.e., we have 
    S(n) != 0 for every natural number n.
*)
Theorem S_n_not_zero : forall n : nat,
    (S n =? 0) = false.
Proof.
    intros n. simpl. reflexivity.
Qed.

(*
    TA Proposition 2.1.6

    4 does not equal 0.
*)
Proposition neq_4_0: (4 =? 0) = false.
Proof. reflexivity. Qed.

(*
    TA Axiom 2.4

    Different natural numbers must have 
    different successors; i.e., if n, m 
    are natural numbers and n != m, then 
    (S n) != (S m). Equivalently, if 
    S(n) = S(m), then we must have n = m.
*)
Theorem S_n_neq_S_m_if_n_neq_m : forall n m : nat, 
    (S n =? S m) = false -> (n =? m) = false.
Proof.
    intros n m H. assert ((n =? m) = (S n =? S m)).
    - reflexivity.
    - rewrite -> H0. rewrite <- H. reflexivity.
Qed.
(* We can assume the inverse *)
Theorem S_n_eq_S_m_if_n_eq_m : forall n m : nat,
    (S n = S m) -> n = m.
Proof. Admitted.

(*
    TA Proposition 2.1.8

    6 does not equal 2.
*)
Proposition neq_6_2: (6 =? 2) = false.
Proof. reflexivity. Qed.

(*
    TA Axiom 2.5

    (Principle of mathematical induction). 
    Let P (n) be any property pertaining 
    to a natural number n. Suppose that 
    P (0) is true, and suppose that 
    whenever P (n) is true, P (n++) is 
    also true. Then P (n) is true for 
    every natural number n.

    Induction is built-in to Coq, so
    we will assume this to be true.
*)

(*
    TA Definition 2.2.1

    Let m be a natural number. To add 
    zero to m, we define 0 + m := m. Now
    suppose inductively that we have 
    defined how to add n to m. Then we 
    can add (S n) to m by defining 
    (S n) + m := S (n + m).
*)
Fixpoint plus (n : nat) (m : nat) : nat :=
    match n with
    | O => m
    | S n' => S (plus n' m)
    end.

Notation "x + y" := (plus x y)
    (at level 50, left associativity)
    : nat_scope.

(*
    TA Lemma 2.2.2

    For any natural number n, n + 0 = n
*)
Lemma add_0_r : forall n : nat,
    n + 0 = n.
Proof.
    intros n. induction n as [| n' IHn'].
    - (* n = 0 *)
        simpl. reflexivity.
    - (* n = S n' *)
        simpl. rewrite -> IHn'. reflexivity.
Qed.

(*
    TA Lemma 2.2.3

    For any natural numbers n and m, 
    n + (S m) = S (n + m).
*)
Lemma S_assoc : forall n m : nat,
    n + (S m) = S (n + m).
Proof.
    intros n m. induction n as [| n' IHn'].
    - (* n = 0 *)
        simpl. reflexivity.
    - (* n = S n' *)
        simpl. rewrite -> IHn'. reflexivity.
Qed.

(*
    TA Proposition 2.2.4

    For any natural numbers n and m, 
    n + m = m + n.
*)
Proposition add_comm : forall n m,
    n + m = m + n.
Proof.
    intros n m. induction n as [| n' IHn'].
    - (* n = 0 *)
        simpl. rewrite -> add_0_r. reflexivity.
    - (* n = S n' *)
        simpl. rewrite -> IHn', S_assoc. reflexivity.
Qed.

(*
    TA Proposition 2.2.5

    For any natural numbers a, b, c, we 
    have (a + b) + c = a + (b + c).
*)
Proposition add_assoc : forall a b c : nat,
    a + (b + c) = (a + b) + c.
Proof.
    intros a b c. induction a as [| a' IHa' ].
    - (* a = 0 *)
        simpl. reflexivity.
    - (* a = S a' *)
        simpl. rewrite -> IHa'. reflexivity.
Qed.

(*
    TA Proposition 2.2.6

    Let a, b, c be natural numbers such 
    that a + b = a + c. Then we have 
    b = c.
*)
Proposition add_cancellation : forall a b c : nat,
    a + b = a + c -> b = c.
Proof.
    intros a b c. induction a as [| a' IHa' ].
    - (* a = 0 *)
        simpl. symmetry. rewrite -> H. reflexivity.
    - (* a = S n' *) 
        simpl. intro H. apply IHa'. congruence.
Qed.

(*
    TA Definition 2.2.7

    A natural number n is said to be 
    positive iff it is not equal to 0.
*)
Definition positive (n : nat) : bool :=
    match n with
    | O => false
    | _ => true
    end.

(*
    TA Proposition 2.2.8

    If a is positive and b is a natural 
    number, then a + b is positive (and 
    hence b + a is also, by Proposition
    2.2.4).
*)
Proposition pos_addition : forall a b : nat,
    positive a = true -> positive (a + b) = true.
Proof.
    intros a b. induction b as [| b' IHb' ].
    - (* b = 0 *)
        rewrite -> add_0_r. symmetry. rewrite -> H. reflexivity.
    - (* b = S b' *)
        rewrite -> S_assoc. simpl. reflexivity.
Qed.

(*
    TA Corollary 2.2.9

    If a and b are natural numbers such 
    that a + b = 0, then a = 0 and b = 0.
*)
Corollary a_b_sum_0 : exists a b : nat,
    a + b = 0 -> a = 0 -> b = 0.
Proof.
    exists 0. exists 0. simpl. reflexivity.
Qed.

Fixpoint leb (n m : nat) : bool :=
    match n with
    | O => true
    | S n' => 
        match m with
        | O => false
        | S m' => leb n' m'
        end
    end.

Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Definition ltb (n m : nat) : bool :=
    (andb (n <=? m) (notb (n =? m))).

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Fixpoint geb (n m : nat) : bool :=
    match n with
    | O => n =? m
    | S n' => 
        match m with
        | O => true
        | S m' => geb n' m'
        end
    end.

Notation "x >=? y" := (geb x y) (at level 70) : nat_scope.

Definition gtb (n m : nat) : bool :=
    notb (leb n m).

Notation "x >? y" := (gtb x y) (at level 70) : nat_scope.

(*
    Proposition 2.2.12 
    
    (Basic properties of order for 
    natural numbers). Let a, b, c be 
    natural numbers. Then
    - (Order follows reflexivity) a >= a.
    - (Order is transitive) If a >= b and 
      b >= c, then a >= c.
    - (Order is anti-symmetric) If 
      a >= b and b >= a, then a = b.
    - (Addition preserves order) a >= b 
      if and only if a + c >= b + c.
    - a < b if and only if a++ ??? b.
    - a < b if and only if b = a + d for 
      some positive number d.
*)
Proposition order_reflexive : forall a : nat,
    a >=? a = true.
Proof.
    intros a. induction a as [| a' IHa'].
    - (* a = 0 *)
        simpl. reflexivity.
    - (* a = S a' *)
        rewrite <- IHa'. reflexivity.
Qed.

Lemma n_geq_0 : forall n : nat,
    n >=? 0 = true.
Proof.
    intros n. induction n as [| n' IHn' ].
    - reflexivity.
    - reflexivity.
Qed. 

Lemma sub_0 : forall n : nat,
    n - 0 = n.
Proof.
    intros n. induction n as [| n' IHn' ].
    - (* n = 0 *)
        reflexivity.
    - (* n = S n' *)
        reflexivity.
Qed.

(*
    After this point, ordering proofs
    become really hard to translate
    to Coq. Tao's proofs are actually
    fairly informal and make lots of
    assumptions that seem obvious but
    are not rigorously proved. I'll
    work on these later but for now I'm
    going to assume that these are true.
*)

Lemma geq_add_n : forall a b : nat, exists n : nat, 
    (a >=? b) = true -> a = b + n.
Proof.
    (* TODO : Come back to this later *)
    Admitted.

Lemma leq_add_n : forall a b : nat, exists n : nat,
    (a <=? b) = true -> a + n = b.
Proof.
    (* TODO *)
    Admitted.

Lemma ineq_inclusive_reversal : forall a b : nat,
    (a <=? b) = (b >=? a).
Proof.
    intros a b. induction b as [| b' IHb' ].
    - induction a as [| a' IHa' ].
        -- reflexivity.
        -- reflexivity.
    - induction a as [| a' IHa' ].
        -- reflexivity.
        (* TODO *)
        -- Admitted.  

Proposition order_transitive : forall a b c : nat,
    a >=? b = true -> b >=? c = true -> a >=? c = true.
Proof.
    intros a b c Hab Hbc. 
    (* TODO *)
    Admitted.

Proposition order_antisymmetric : forall a b : nat,
    (a >=? b) = (b >=? a) -> b = a.
Proof.
    intros a b.
    assert (X: exists n : nat, (a >=? b) = true -> a = b + n).
    {
        apply geq_add_n.
    }
    destruct X as [n ?].
    (* TODO *)
    Admitted.

Proposition addition_preserves_order : forall a b c : nat,
    (a + c >=? b + c) = true -> (a >=? b) = true.
Proof.
    intros a b c H.
    (* TODO *)
    Admitted.

Proposition S_leq_le : forall a b : nat,
    (S a <=? b) = (a <? b).
Proof.
    intros a b. induction a as [| a' IHa' ].
    - (* a = 0 *) 
        induction b as [| b' IHb' ].
        -- reflexivity.
        -- reflexivity.
    - (* a = S a' *) 
        
    (* TODO *)
    Admitted.

Proposition a_lt_b_for_sum_a_d_eq_b : forall a b : nat, exists d : nat,
    (b = a + d) -> (a <? b) = true.
Proof.
    intros a b. 
    (* TODO *)
    Admitted.

(* 
    TA Definition 2.3.1
*)
Fixpoint mult (n m : nat) : nat :=
    match n with
    | O => O
    | S n' => plus m (mult n' m)
    end.

Notation "x * y" := (mult x y)
    (at level 40, left associativity)
    : nat_scope.

Lemma mul_0_r : forall n : nat,
    n * 0 = 0.
Proof.
    intros n. induction n as [| n' IHn' ].
    - (* n = 0 *)
        simpl. reflexivity.
    - (* n = S n' *)
        simpl. rewrite -> IHn'. reflexivity.
Qed.

Lemma mul_n_Sk : forall n k : nat,
    n * (S k) = n + (n * k).
Proof.
    intros n k. induction n as [| n' IHn' ].
    - (* n = 0 *)
        simpl. reflexivity.
    - (* n = S n' *)
        simpl. rewrite -> IHn', add_assoc, add_assoc.
        assert (k + n' = n' + k) as H.
        {
            rewrite -> add_comm. reflexivity.
        }
        rewrite -> H. reflexivity.
Qed.

(*
    Lemma 2.3.2
    
    Let n, m be natural numbers. Then 
    n * m = m * n.
*)
Lemma mul_comm : forall m n : nat,
    n * m = m * n.
Proof.
    intros n m. induction n as [| n' IHn' ].
    - (* n = 0 *)
        simpl. rewrite -> mul_0_r. reflexivity.
    - (* n = S n' *)
        simpl. rewrite <- IHn'.
        rewrite -> mul_n_Sk. reflexivity.
Qed.

(*
    Lemma 2.3.3

    Let n, m be natural numbers. Then 
    n * m = 0 if and only if at least 
    one of n, m is equal to zero. In 
    particular, if n and m are both 
    positive, then nm is also positive.
*)
Theorem nat_no_zero_divisors : forall n m : nat,
    andb (positive n) (positive m) =  (positive (n * m)).
Proof.
    intros n m. induction n as [| n' IHn' ].
    - (* n = 0 *)
        simpl. reflexivity.
    - (* n = S n' *)
        simpl. induction m as [| m' IHm' ].
        -- (* m = 0 *)
            simpl. rewrite -> mul_0_r. reflexivity.
        -- (* m = S m' *)
            simpl. reflexivity.
Qed.

(*
    Proposition 2.3.4

    For any natural numbers a, b, c, we 
    have a(b + c) = ab + ac and 
    (b + c)a = ba + ca.
*)
Proposition mul_distribution : forall a b c : nat,
    a * (b + c) = (a * b) + (a * c).
Proof.
    intros a b c. induction c as [| c' IHc' ].
    - (* c = 0 *)
        rewrite -> add_0_r, mul_0_r, add_0_r.
        reflexivity.
    - (* c = S c' *)
        rewrite -> add_comm. simpl.
        rewrite -> mul_n_Sk.
        assert (c' + b = b + c').
            { rewrite -> add_comm. reflexivity. }
        rewrite -> add_comm, H, mul_n_Sk.
        assert (a + a * c' = a * c' + a).
            { rewrite -> add_comm. reflexivity. }
        rewrite -> IHc', H0, add_assoc. reflexivity.
Qed.

(*
    Proposition 2.3.5

    For any natural numbers a, b, c, we 
    have (a * b) * c = a * (b * c).
*)
Proposition mul_assoc : forall a b c : nat,
    (a * b) * c = a * (b * c).
Proof.
    intros a b c. induction c as [| c' IHc' ].
    - (* c = 0 *)
        rewrite -> mul_0_r, mul_0_r, mul_0_r.
        reflexivity.
    - (* c = S c' *)
        rewrite -> mul_n_Sk, mul_n_Sk.
        rewrite -> mul_distribution.
        assert (a * (b * c') = a * b * c').
        { rewrite <- IHc'. reflexivity. }
        rewrite -> H. reflexivity.
Qed.

(*
    Proposition 2.3.6

    If a, b are natural numbers such 
    that a < b, and c is positive, 
    then ac < bc.
*)
Proposition mul_preserves_order : forall a b c : nat,
    a < b -> (positive c) = true -> (a * c) <? (b * c) = true.
Proof.
    intros a b c.
    (* TODO : based on ordering proofs *)
    Admitted.

(*
    Corollary 2.3.7

    Let a, b, c be natural numbers such 
    that ac = bc and c is non-zero. 
    Then a = b
*)
Corollary mul_cancellation : forall a b c : nat,
    (a * c = b * c) /\ (c <> 0) -> a = b.
Proof.
    intros a b c H. 
    (* TODO : still can't figure out these logic-gate proofs *)
    Admitted.

(*
    Proposition 2.3.9

    Let n be a natural number, and let q 
    be a positive number. Then there 
    exist natural numbers m, r such that 
    0 <= r < q and n = mq + r.
*)

(* TODO : not sure how to formulate this theorem *)

(*
    Definition 2.3.11
*)
Fixpoint exp (base power : nat) : nat :=
    match power with
    | O => S O
    | S p => mult base (exp base p)
    end.

Notation "x ** y" := (exp x y)
    (at level 30, right associativity)
    : nat_scope.

Theorem mul_1_r : forall n : nat,
    n * 1 = n.
Proof.
    intros n. induction n as [| n' IHn' ].
    - (* n = 0 *)
        simpl. reflexivity.
    - (* n = S n' *)
        simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem pow_2_mul_self : forall n : nat,
    n ** 2 = n * n.
Proof.
    intros n. induction n as [| n' IHn' ].
    - (* n = 0 *)
        simpl. reflexivity.
    - (* n = S n' *)
        simpl. rewrite -> mul_1_r. reflexivity.
Qed.

Theorem foil : forall a b c d : nat,
    (a + b) * (c + d) = a * c + c * b + a * d + b * d.
Proof.
    intros a b c d. induction a as [| a' IHa' ].
    - (* a = 0 *)
        simpl. rewrite -> add_0_r. rewrite -> mul_distribution, mul_comm. reflexivity.
    - (* a = S a' *)
        assert ((S a' + b) * (c + d) = (S a' + b) * c + (S a' + b) * d).
        {
            rewrite -> mul_distribution. reflexivity.
        }
        rewrite -> H. rewrite -> mul_comm, mul_distribution.
        assert ((S a' + b) * d = S a' * d + b * d).
        {
            rewrite -> mul_comm, mul_distribution.
            rewrite -> mul_comm.
            assert (d * b = b * d).
            {
                rewrite -> mul_comm. reflexivity.
            }
            rewrite -> H0. reflexivity.
        }
        rewrite -> H0, add_assoc.
        assert (c * S a' = S a' * c).
        {
            rewrite -> mul_comm. reflexivity.
        }
        rewrite -> H1.
        reflexivity.
Qed.

Theorem sum_n_n_eq_2n : forall n : nat,
    n + n = 2 * n.
Proof.
    intros n. induction n as [| n' IHn' ].
    - reflexivity.
    - simpl. rewrite -> add_0_r. reflexivity.
Qed. 

(*
    Exercise 2.3.4
*)
Theorem ex_2_3_4 : forall a b : nat,
    (a + b) ** 2 = a ** 2 + (2 * a * b) + b ** 2.
Proof.
    intros a b. induction a as [| a' IHa' ].
    - (* a = 0 *)
        simpl. reflexivity.
    - (* a = S a' *)
        rewrite -> pow_2_mul_self, foil.
        rewrite <- pow_2_mul_self.
        rewrite <- pow_2_mul_self.
        assert (S a' * b + S a' * b = 2 * S a' * b).
        {
            rewrite -> sum_n_n_eq_2n, mul_assoc. reflexivity. 
        }
        rewrite <- H, add_assoc. reflexivity.
Qed.

(*
    Sets of natural numbers
*)

Definition nat_multiset := multiset nat.

(*
    Inspired by TA 3.1.4
*)
Fixpoint multiplicity  (m : nat_multiset) (a : nat) : nat :=
    match m with 
    | empty => 0
    | h :: t => match h =? a with
        | true => 1 + (multiplicity t a)
        | false => multiplicity t a
        end
    end.

Fixpoint nm_is_subset (m1 m2 : nat_multiset) : bool :=
    match m1 with
    | empty => true
    | h :: t => match (multiplicity m1 h =? multiplicity m2 h) with
        | true => match t with 
            | empty => true
            | _ => nm_is_subset t m2
            end
        | false => false
        end
    end.

Definition nm_eq (m1 m2 : nat_multiset) : bool :=
    nm_is_subset m1 m2 && nm_is_subset m2 m1.

Notation "x =? y" := (nm_eq x y) (at level 70).

Definition nm_is_proper_subset (m1 m2 : nat_multiset) :=
    (nm_is_subset m1 m2) && notb (nm_eq m1 m2).

Lemma empty_subset_all : forall m : nat_multiset,
    nm_is_subset {} m = true.
Proof.
    intros m. simpl. reflexivity.
Qed.

Lemma set_is_own_subset : forall m : nat_multiset,
    nm_is_subset m m = true.
Proof.
    intros m. unfold nm_is_subset.
    (* TODO : Come back to this. Seems tough! *)
    Admitted.

(*
    Exercise 3.1.1
*)
Lemma nm_eq_reflexive : forall (m1 : nat_multiset),
    m1 =? m1 = true.
Proof.
    intros m1. unfold nm_eq. rewrite -> b_and_b_is_b.
    rewrite -> set_is_own_subset. reflexivity.
Qed. 

Fixpoint minus (n m:nat) : nat :=
    match n, m with
    | O , _ => O
    | S _ , O => n
    | S n', S m' => minus n' m'
    end.
