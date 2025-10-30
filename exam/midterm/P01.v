Require Export D.



(** [10 points]
 *)

Lemma forall_not_ex_not: forall (X: Type) (P: X -> Prop)
    (ALL: forall x, P x),
  ~ exists x, ~ P x.
Proof.
  exact FILL_IN_HERE.
Qed.

