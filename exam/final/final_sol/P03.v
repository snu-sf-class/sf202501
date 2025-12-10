Require Export P02.



(** Find the weakest precondition [WP] of [X := 2*X + Y] for postcondition [3*X - 2*Y < 10]

      {{ WP }} X := 2*X + Y {{ 3*X - 2*Y < 10 }}

    and prove it correct (10 points).
 *)

Definition WP : Assertion :=
  assert (3*(2*X + Y) - 2*Y < 10).

(* You can use [hauto_vc]. *)
Theorem WP_weakest: forall P
    (PRE: {{ P }} X := 2*X + Y {{ 3*X - 2*Y < 10 }}),
  P ->> WP.
Proof.
  intros. unfold WP. red in PRE. red; intros.
  hexploit PRE; eauto using ceval; intros.
  destruct H0 as [st' [Hx Hy]].
  inversion Hx. subst.
  hauto_vc.
Qed.

