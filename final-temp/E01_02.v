Require Import P01.



Check WP_weakest: forall P
    (PRE: {{ P }} X := 2 * X; Y := (X-1) / Y {{ X < Y }}),
  P ->> WP.

