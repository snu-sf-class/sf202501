Require Import P05.



Check bubble_sort_correct: forall (array: list nat),
  let size := Lists.List.length array
  in
  valid_hoare_triple
    (fun st => st SIZE = size /\ arr2list (st ARRAY) size = array)
      bubble_sort_com
    (fun st => Sorted (arr2list (st ARRAY) size) /\
               Permutation (arr2list (st ARRAY) size) array).
