Require Import P07.



Check tmfib_bias : tm.

Check tmfib_bias_correct: forall (n: nat),
   <{{ tmfib_bias n }}> ==>* (tm_const (fib_bias n)).

