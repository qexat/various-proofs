Require Import Arith.
Require Import ZArith.
Require Import Coq.Classes.RelationClasses.

Open Scope Z_scope.

Definition abs (n : Z) := if n >=? 0 then n else (- n).

Lemma abs_ge_0 : forall (n : Z), abs n >= 0.
Proof.
  induction n.
  - cbn. apply Z.ge_le_iff. reflexivity.
  - apply Zge_cases with (n := Z.pos p) (m := 0).
  - apply Z.geb_ge. auto.
Qed.

Close Scope Z_scope.
