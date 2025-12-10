Require Import P01.



Check aexp_subst_eval: forall x a1 a2 st,
  aeval st (aexp_subst x a1 a2) = aeval (x !-> aeval st a1; st) a2.

