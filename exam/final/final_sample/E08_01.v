Require Import P08.



Check prime_check_correct: forall (n: nat) (POS: n > 2),
  {{ N = n }} 
    prime_check_com
  {{ (RES = 1) <-> prime n }}.

