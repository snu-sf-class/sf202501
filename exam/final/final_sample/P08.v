Require Export P07.



(** Verify the [prime_check_com] program (20 points).

    Hint: You can also use [hauto_vc] to simplify the goal.
 *)

(*
Definition prime_check_com : com := <{
    RES := 1;
    I := 2;      
    T := N / I;
    if N = T * I
    then RES := 0
    else
      I := 3;
      while ((I * I <= N) && (RES = 1)) do
        T := N / I;
        if N = T * I then RES := 0 else skip end;
        I := I + 2
      end      
    end      
 }>.

Definition divisible d n : Prop :=
  exists q, n = d*q.

Definition prime (p: nat) : Prop :=
  (p > 1) /\
  (forall d (DIV: divisible d p), d = 1 \/ d = p).
*)

Theorem prime_check_correct: forall (n: nat) (POS: n > 2),
  {{ N = n }} 
    prime_check_com
  {{ (RES = 1) <-> prime n }}.
Proof.
  intros. unfold prime_check_com.
  exact FILL_IN_HERE.
Qed.

