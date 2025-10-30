Require Export P01.



(** [10 points]
 *)

Theorem disj_impl_all: forall X (P Q R: X -> Prop)
    (EX: exists x, P x \/ Q x)
    (PR: forall x, P x -> R x)
    (QR: forall x, Q x -> R x),
  exists x, R x.
Proof.
  exact FILL_IN_HERE.
Qed.

