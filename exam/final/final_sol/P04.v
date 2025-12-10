Require Export P03.



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

(** Write an Imp program [sort_two_com] that sorts in the increasing order
    the values in the variables 'X' and 'Y', and prove it correct (10 points).

    Avaiable Vairable Names: F, G, X, Y, Z, I, J, P, T, N, RES
 *)

Definition sort_two_com : com :=
  <{
    if X <= Y then skip else
      Z := X;
      X := Y;
      Y := Z
    end
  }>
.

Theorem sort_two_com_correct: forall n m: nat,
  {{ X = n /\ Y = m }}
     sort_two_com
  {{ X <= Y /\ ((X = n /\ Y = m) \/ (X = m /\ Y = n)) }}.
Proof.
  unfold sort_two_com. intros.
  (* You should be able to prove the goal by [hauto]
     if you wrote [sort_two_com] correctly. *)  
  hauto.
Qed.

