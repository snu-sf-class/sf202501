Require Import P03.



Check WP : Assertion.

Check WP_weakest: forall P
    (PRE: {{ P }} X := 2*X + Y {{ 3*X - 2*Y < 10 }}),
  P ->> WP.

