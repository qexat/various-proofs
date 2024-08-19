Require Import Arith.
Require Import Nat.
Require Import Lia.

Lemma remarkable_identity_1 : forall (n m : nat), (n + m) ^ 2 = (n ^ 2) + (2 * n * m) + (m ^ 2).
Proof.
  intros n m.
  replace ((n + m) ^ 2) with ((n + m) * (n + m)).
  - simpl. ring.
  - rewrite Nat.pow_2_r with (a := n + m). reflexivity.
Qed.

Lemma remarkable_identity_3 : forall (n m : nat), n ^ 2 - m ^ 2 = (n - m) * (n + m).
Proof.
  intros n m.

  rewrite Nat.pow_2_r with (a := n).
  rewrite Nat.pow_2_r with (a := m).
  rewrite Nat.mul_sub_distr_r with (p := (n + m)).
  rewrite Nat.mul_add_distr_l with (m := n) (p := m).
  rewrite Nat.mul_add_distr_l with (n := m) (m := n) (p := m).
  rewrite Nat.sub_add_distr with (n := n * n + n * m) (m := m * n) (p := m * m).
  rewrite Nat.mul_comm with (n := m) (m := n).

  lia.
Qed.
