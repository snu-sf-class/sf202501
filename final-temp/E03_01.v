Require Import P03.



Check sum_com_ex1:
  exists st, (N !-> 2) =[ sum_com ]=> Some st /\ st RES = 3.

Check sum_com_ex2:
  exists st, (N !-> 3) =[ sum_com ]=> Some st /\ st RES = 6.

