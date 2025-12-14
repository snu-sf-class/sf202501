Require Import P03.



Check sum_com_correct: forall n: nat,
  {{ N = n }}
     sum_com
  {{ RES = #sum_to_n n }}.

