Require Import P04.



Check tmlist_sum_correct: forall (l: list nat),
    let tm := to_tmlist l in
    let n := sum_list l in
    <{{ tmlist_sum tm }}> ==>* n.

