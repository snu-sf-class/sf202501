Require Export D.



(** Find the weakest precondition [WP] of [X := 2 * X; X := (X-1) / (Y+1)] for postcondition [X < Y]

      {{ WP }} X := 2 * X; Y := (X-1) / Y {{ X < Y }}

    and prove it correct (10 points).

    Hint: Use [hauto_vc].
 *)

(** 10 pts **)

Definition WP : Assertion :=
  (assert True)%Aexp
  .

Theorem WP_correct:
  {{ WP }} X := 2 * X; Y := (X-1) / Y {{ X < Y }}.
Proof.
  exact FILL_IN_HERE. (* unfold WP. hauto. *)
Qed.

(** 10 pts **)

(* You can use [hauto_vc]. *)
Theorem WP_weakest: forall P
    (PRE: {{ P }} X := 2 * X; Y := (X-1) / Y {{ X < Y }}),
  P ->> WP.
Proof.
  exact FILL_IN_HERE.
Qed.

