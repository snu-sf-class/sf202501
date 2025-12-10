Require Import P04.



Check sort_two_com : com.

Check sort_two_com_correct: forall n m: nat,
  {{ X = n /\ Y = m }}
     sort_two_com
  {{ X <= Y /\ ((X = n /\ Y = m) \/ (X = m /\ Y = n)) }}.

