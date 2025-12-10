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
  <{{
  fix (\F:Nat->Nat, \N:Nat,
       if0 N then 0 else (if0 (N-1) then 1 else 2 * F(N-1)) + F(N-2)
  )
  }}>
.

Example tmfib_bias_type: empty |-- tmfib_bias \in (Nat -> Nat).
Proof.
  repeat econstructor.
Qed.

Example tmfib_bias_ex1: <{{ tmfib_bias 4 }}> ==>* <{{ 12 }}>.
Proof.
  unfold tmfib_bias. normalize.
Qed.

Example tmfib_bias_ex2: <{{ tmfib_bias 5 }}> ==>* <{{ 29 }}>.
Proof.
  unfold tmfib_bias. normalize.
Qed.

Example tmfib_bias_ex3: <{{ tmfib_bias 6 }}> ==>* <{{ 70 }}>.
Proof.
  unfold tmfib_bias. normalize.
Qed.

(** Correctness:

   Hint: 

   Use the tactic [normalize1], which takes one-step of execution.
     (e.g.) [do 5 normalize1] takes 5 steps of execution.
   You can use the tactic [normalize], which takes steps as many as possible.

   Proving the following lemma might be useful.
   [forall (n: nat) t t', t ==>* t' -> <{{ n * t }}> ==>* <{{ n * t' }}>]
 *)

Lemma tmult_compat2: forall (n: nat) t t',
  t ==>* t' ->
  <{{ n * t }}> ==>* <{{ n * t' }}>.
Proof.
  intros; induction H; subst; eauto.
Qed.

Lemma tplus_compat1: forall t t' s,
  t ==>* t' ->
  <{{ t + s }}> ==>* <{{ t' + s }}>.
Proof.
  intros; induction H; subst; eauto.
Qed.

Lemma tplus_compat2: forall (n: nat) t t',
  t ==>* t' ->
  <{{ n + t }}> ==>* <{{ n + t' }}>.
Proof.
  intros; induction H; subst; eauto.
Qed.

Arguments fib_bias n : simpl never.

Theorem tmfib_bias_correct: forall (n: nat),
   <{{ tmfib_bias n }}> ==>* (tm_const (fib_bias n)).
Proof.
  assert (forall n m, m <= n -> <{{ tmfib_bias m }}> ==>* fib_bias m); eauto.
  unfold tmfib_bias. intros. normalize1.
  revert m H. induction n; intros.
  - inversion H; subst.
    normalize.
  - destruct m; [normalize|].
    destruct m; [normalize|].
    do 6 normalize1.
    eapply multi_trans.
    + eapply tplus_compat1.
      eapply tmult_compat2.
      eapply IHn. nia.
    + normalize1.
      eapply multi_trans.
      * eapply tplus_compat2.
        do 2 normalize1.
        rewrite sub_0_r.
        eapply IHn. nia.
      * normalize.
Qed.

