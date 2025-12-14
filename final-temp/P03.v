Require Export P02.



(** *** The following is an example of an Imp program. *)

Definition slow_sub_com (m n: nat) : com :=
  <{
    X := m;
    Z := n;
    while ~(X = 0) do
      Z := Z - 1;
      X := X - 1
    end
  }>.

(** End **)

(** (10 pts)
 Write an Imp program [sum_com] that takes an input from 'N' and writes an output to 'RES',
 where the output should be 1 + 2 + ... + 'N'.

 Available Variable Names: F, G, X, Y, Z, I, J, P, T, N, SELF, RES
*)

Definition sum_com : com :=
  FILL_IN_HERE
  .

Example sum_com_ex1:
  exists st, (N !-> 2) =[ sum_com ]=> Some st /\ st RES = 3.
Proof.
  exact FILL_IN_HERE.
  (* eexists; split; [ceval_steps|unfold t_update; simpl; eauto]. *)
Qed.

Example sum_com_ex2:
  exists st, (N !-> 3) =[ sum_com ]=> Some st /\ st RES = 6.
Proof.
  exact FILL_IN_HERE.
  (* eexists; split; [ceval_steps|unfold t_update; simpl; eauto]. *)
Qed.

(** (10 pts)
 Prove that [sum_com] is correct.
*)
Theorem sum_com_correct: forall n: nat,
  {{ N = n }}
     sum_com
  {{ RES = #sum_to_n n }}.
Proof.
  unfold sum_com.
  exact FILL_IN_HERE.
Qed.

