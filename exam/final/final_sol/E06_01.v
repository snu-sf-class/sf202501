Require Import P06.



Check slow_fact_correct: forall (n: nat),
  {{ N = n }} 
    slow_fact_com
  {{ RES = fact n }}.

