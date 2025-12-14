Require Import P02.



Check optimize_if_while_correct: forall st st' c,
  (st =[ c ]=> st') -> (st =[ optimize_if_while c ]=> st').

