Require Import P05.



Check swap_permutation: forall i (l: list nat)
  (RANGE: i + 1 < Lists.List.length l),
  Permutation
    (set_nth (i+1) (Lists.List.nth i l 0) (set_nth i (nth (i+1) l 0) l))
    l.

