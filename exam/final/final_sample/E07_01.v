Require Import P07.



Check tmfib_bias : tm.

Check tmfib_bias_type: empty |-- tmfib_bias \in (Nat -> Nat).

Check tmfib_bias_ex1: <{{ tmfib_bias 4 }}> ==>* <{{ 12 }}>.

Check tmfib_bias_ex2: <{{ tmfib_bias 5 }}> ==>* <{{ 29 }}>.

Check tmfib_bias_ex3: <{{ tmfib_bias 6 }}> ==>* <{{ 70 }}>.

