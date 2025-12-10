Require Export P04.



(** *** The following is an example of verification using hauto. *)

Lemma slow_sub_correct: forall (m n: nat),
  {{ True }} slow_sub_com m n {{ Z = n - m }}.
Proof.
  unfold slow_sub_com. intros.
  hauto.
  - hauto_while (assert (Z - X = n - m)).
  - hauto.
Qed.

(** End **)

(** Verify the [odd_sum_com] program (10 points).

    Hint: You can also use [hauto_vc] to simplify the goal.
 *)

(*
Definition odd_sum_com : com := <{
  RES := 0 ;
  I := 0 ;
  J := 1 ;
  while ~(I = N) do
    RES := RES + J;
    I := I + 1;
    J := J + 2
  end }>.
*)
  
Theorem odd_sum_correct: forall (n: nat),
  {{ N = n }} 
    odd_sum_com
  {{ RES = n * n }}.
Proof.
  intros. unfold odd_sum_com.
  exact FILL_IN_HERE.
Qed.

