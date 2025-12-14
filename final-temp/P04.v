Require Export P03.



(** *** The following is an example of a STLC program, and a test. *)

Definition tmsquare : tm := <{{ \X:Nat, X * X }}>.
  
Example tmsquare_test: <{{ tmsquare 3 }}> ==>* 9.
Proof.
  unfold tmsquare.
  normalize.
Qed.

(** End **)

(**  Write a lamba term [tmlist_sum] of type (List Nat -> Nat) that
     computes the summation of all elements in the given list (10 points)
     and prove it correct (10 points).

     Available Variable Names: F, G, X, Y, Z, I, J, P, T, N, SELF, RES
 *)

Definition tmlist_sum : tm :=
  (* Use parenthesis inside each case clause; otherwise, parsing may work incorrectly *)
  FILL_IN_HERE
  .

Example tmlist_sum_type: empty |-- tmlist_sum \in (List Nat -> Nat).
Proof.
  exact FILL_IN_HERE.
  (* repeat econstructor. *)
Qed.

Example tmlist_sum_ex1: <{{ tmlist_sum (1::0::3::nil Nat) }}> ==>* <{{ 4 }}>.
Proof.
  exact FILL_IN_HERE.
  (* unfold tmlist_sum. normalize. *)
Qed.

Example tmlist_sum_ex2: <{{ tmlist_sum (3::7::nil Nat) }}> ==>* <{{ 10 }}>.
Proof.
  exact FILL_IN_HERE.
  (* unfold tmlist_sum. normalize. *)
Qed.

Example tmlist_sum_ex3: <{{ tmlist_sum (2::nil Nat) }}> ==>* <{{ 2 }}>.
Proof.
  exact FILL_IN_HERE.
  (* unfold tmlist_sum. normalize. *)
Qed.

(** Correctness:

   Hint: 

   Use the tactic [normalize1], which takes one-step of execution.
     (e.g.) [do 5 normalize1] takes 5 steps of execution.
   You can use the tactic [normalize], which takes steps as many as possible.

 *)

Lemma to_tmlist_value: forall l,
    value (to_tmlist l).
Proof.
  induction l; econstructor; eauto.
Qed.

Lemma plus_congruence_l:
  forall t t' t2, t ==>* t' -> <{{ t + t2 }}> ==>* <{{ t' + t2 }}>.
Proof.
  intros. induction H; subst; eauto.
Qed.

Lemma plus_congruence_r:
  forall v t t', value v -> t ==>* t' -> <{{ v + t }}> ==>* <{{ v + t' }}>.
Proof.
  intros. induction H0; subst; eauto.
Qed.

Theorem tmlist_sum_correct: forall (l: list nat),
    let tm := to_tmlist l in
    let n := sum_list l in
    <{{ tmlist_sum tm }}> ==>* n.
Proof.
  exact FILL_IN_HERE.
Qed.

