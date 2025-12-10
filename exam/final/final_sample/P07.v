Require Export P06.



(** *** The following is an example of a STLC program, and a test. *)

Definition tmsquare : tm := <{{ \X:Nat, X * X }}>.
  
Example tmsquare_test: <{{ tmsquare 3 }}> ==>* 9.
Proof.
  unfold tmsquare.
  normalize.
Qed.

(** End **)

(** A biased fibonacci function is defined as follows.

    Fixpoint fib_bias n :=
      match n with 
      | 0 => 0
      | S n' =>
        match n' with
        | 0 => 1
        | S n'' => 2 * fib_bias n' + fib_bias n''         
        end
      end.

    Write a lamba term [tmfib_bias] of type (TNat -> TNat) that computes the biased fibonacci function (10 points)
    and prove it correct (10 points).

    Avaiable Vairable Names: F, G, X, Y, Z, I, J, P, T, N, RES
 *)

Definition tmfib_bias : tm :=
  FILL_IN_HERE
.

Example tmfib_bias_type: empty |-- tmfib_bias \in (Nat -> Nat).
Proof.
  exact FILL_IN_HERE.
  (* repeat econstructor. *)
Qed.

Example tmfib_bias_ex1: <{{ tmfib_bias 4 }}> ==>* <{{ 12 }}>.
Proof.
  exact FILL_IN_HERE.
  (* unfold tmfib_bias. normalize. *)
Qed.

Example tmfib_bias_ex2: <{{ tmfib_bias 5 }}> ==>* <{{ 29 }}>.
Proof.
  exact FILL_IN_HERE.
  (* unfold tmfib_bias. normalize. *)
Qed.

Example tmfib_bias_ex3: <{{ tmfib_bias 6 }}> ==>* <{{ 70 }}>.
Proof.
  exact FILL_IN_HERE.
  (* unfold tmfib_bias. normalize. *)
Qed.

(** Correctness:

   Hint: 

   Use the tactic [normalize1], which takes one-step of execution.
     (e.g.) [do 5 normalize1] takes 5 steps of execution.
   You can use the tactic [normalize], which takes steps as many as possible.

   Proving the following lemma might be useful.
   [forall (n: nat) t t', t ==>* t' -> <{{ n * t }}> ==>* <{{ n * t' }}>]
 *)

Theorem tmfib_bias_correct: forall (n: nat),
   <{{ tmfib_bias n }}> ==>* (tm_const (fib_bias n)).
Proof.
  unfold tmfib_bias. intros.
  exact FILL_IN_HERE.
Qed.

