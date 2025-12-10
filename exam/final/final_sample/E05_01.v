Require Import P05.



Check odd_sum_correct: forall (n: nat),
  {{ N = n }} 
    odd_sum_com
  {{ RES = n * n }}.

