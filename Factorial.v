Require Import Arith.
Require Import Nat.

Fixpoint factorial (n : nat) : nat := match n with
  | 0 | 1 => 1
  | S m => n * (factorial m)
end.

Lemma n_le_mul_succ_m_n : forall (n m : nat), n <= (S m) * n.
Proof.
  induction m as [| m IHm].
  - rewrite Nat.mul_1_l. reflexivity.
  - rewrite Nat.mul_succ_l. apply Nat.le_add_l.
Qed.

Lemma factorial_growing_sequence : forall (n : nat), (factorial n) <= (factorial (n + 1)).
Proof.
  induction n as [| n IHn].
  { cbn. reflexivity. }
  {
    rewrite Nat.add_succ_r.
    rewrite Nat.add_0_r.
    replace (factorial (S (S n))) with ((S (S n)) * factorial (S n)) ; remember (S n) as m.
    - apply n_le_mul_succ_m_n.
    - cbn. rewrite Heqm. reflexivity.
  }
Qed.
