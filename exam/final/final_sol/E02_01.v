Require Import P02.



Check optimize_asgn_correct: forall st st' c,
  (st =[ c ]=> st') -> (st =[ optimize_asgn c ]=>st').

