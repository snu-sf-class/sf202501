Require Export P01.



(** Prove the correctness of [optimize_asgn] (10 points). *)

Theorem optimize_if_while_correct: forall st st' c,
  (st =[ c ]=> st') -> (st =[ optimize_if_while c ]=> st').
Proof.
  exact FILL_IN_HERE.
Qed.

