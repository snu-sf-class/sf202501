Require Import P01.



Check WP_correct:
  {{ WP }} X := 2 * X; Y := (X-1) / Y {{ X < Y }}.

