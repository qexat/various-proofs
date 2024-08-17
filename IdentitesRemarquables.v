Require Import Nat.
Require Import Arith.

Lemma carre_n_est_n_fois_n : forall (n : nat), n ^ 2 = n * n.
Proof.
  intro n.
  simpl.
  ring.
Qed.

Lemma identite_remarquable_1 : forall (n m : nat), (n + m) ^ 2 = (n ^ 2) + (2 * n * m) + (m ^ 2).
Proof.
  intros n m.
  replace ((n + m) ^ 2) with ((n + m) * (n + m)).
  - simpl. ring.
  - remember (n + m) as a. rewrite carre_n_est_n_fois_n. reflexivity.
Qed.
