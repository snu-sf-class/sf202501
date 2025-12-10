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
  hauto.
  - hauto_while (fun st => st RES * fact (st N) = fact n).
    + hauto_while (fun st => st J * fact (st N) = fact n /\
                             st RES = st J * st I /\ st I >= 1).
      hauto_vc.
      destruct (st N); try nia.
      simpl in *. rewrite sub_0_r. nia.
    + hauto_vc.
    + hauto_vc.
      rewrite H0 in H. simpl in *. nia.
  - hauto_vc.
Qed.

