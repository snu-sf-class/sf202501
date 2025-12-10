Require Export P05.



(** Verify the [slow_fact_com] program (10 points).

    Hint: You can also use [hauto_vc] to simplify the goal.
 *)

(*
Definition slow_fact_com : com := <{
  RES := 1 ;
  while ~ (N = 0) do
    J := RES;
    I := 1;
    while ~ (I = N) do
      RES := RES + J;
      I := I + 1
    end;
    N := N - 1
  end }>.

Fixpoint fact n :=
  match n with 
  | 0 => 1 
  | S m => n * fact m 
  end.
*)

Theorem slow_fact_correct: forall (n: nat),
  {{ N = n }} 
    slow_fact_com
  {{ RES = fact n }}.
Proof.
  intros. unfold slow_fact_com.
  exact FILL_IN_HERE.
Qed.

