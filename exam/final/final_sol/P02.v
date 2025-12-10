Require Export P01.



(** Prove the correctness of [optimize_asgn] (10 points). *)

Theorem optimize_asgn_correct: forall st st' c,
  (st =[ c ]=> st') -> (st =[ optimize_asgn c ]=>st').
Proof.
  intros. induction H; simpl; eauto; cycle 1.
  - destruct c1; eauto.
    inversion H.
  - destruct c1; eauto.
    destruct c2; eauto.
    destruct (eqb_string x x0) eqn: EQN; eauto.
    apply eqb_string_true_iff in EQN. subst.
    inversion H; subst. inversion H0; subst.
    rewrite t_update_shadow.
    rewrite <-aexp_subst_eval. eauto.
Qed.

