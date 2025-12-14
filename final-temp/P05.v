Require Export P04.



(* 10 points *)

Lemma swap_permutation: forall i (l: list nat)
  (RANGE: i + 1 < Lists.List.length l),
  Permutation
    (set_nth (i+1) (Lists.List.nth i l 0) (set_nth i (nth (i+1) l 0) l))
    l.
Proof.
  exact FILL_IN_HERE.
Qed.

(* 20 points *)
(* Hint: use [Permutation], [SortedRange], [Bounded] when describing the invariant. *)

Theorem bubble_sort_correct: forall (array: list nat),
  let size := Lists.List.length array
  in
  valid_hoare_triple
    (fun st => st SIZE = size /\ arr2list (st ARRAY) size = array)
      bubble_sort_com
    (fun st => Sorted (arr2list (st ARRAY) size) /\
               Permutation (arr2list (st ARRAY) size) array).
Proof.
  unfold bubble_sort_com.
  exact FILL_IN_HERE.
Qed.

