Require Import P03.



Check square_sum_correct: forall n,
    6 * square_sum n = n * (n+1) * (2*n + 1).

