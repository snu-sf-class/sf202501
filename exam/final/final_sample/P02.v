Require Export P01.



(** Prove the correctness of [optimize_asgn] (10 points). *)

Theorem optimize_asgn_correct: forall st st' c,
  (st =[ c ]=> st') -> (st =[ optimize_asgn c ]=>st').
Proof.
  exact FILL_IN_HERE.
Qed.

