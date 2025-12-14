Require Import P04.



Check tmlist_sum_type: empty |-- tmlist_sum \in (List Nat -> Nat).

Check tmlist_sum_ex1: <{{ tmlist_sum (1::0::3::nil Nat) }}> ==>* <{{ 4 }}>.

Check tmlist_sum_ex2: <{{ tmlist_sum (3::7::nil Nat) }}> ==>* <{{ 10 }}>.

Check tmlist_sum_ex3: <{{ tmlist_sum (2::nil Nat) }}> ==>* <{{ 2 }}>.

