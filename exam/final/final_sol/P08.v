Require Export P07.



(** Verify the [prime_check_com] program (20 points).

    Hint: You can also use [hauto_vc] to simplify the goal.
 *)

(*
Definition prime_check_com : com := <{
    RES := 1;
    I := 2;      
    T := N / I;
    if N = T * I
    then RES := 0
    else
      I := 3;
      while ((I * I <= N) && (RES = 1)) do
        T := N / I;
        if N = T * I then RES := 0 else skip end;
        I := I + 2
      end      
    end      
 }>.

Definition divisible d n : Prop :=
  exists q, n = d*q.

Definition prime (p: nat) : Prop :=
  (p > 1) /\
  (forall d (DIV: divisible d p), d = 1 \/ d = p).
*)

Definition indivisible_upto i (p: nat) : Prop :=
  (p > 1) /\
  (forall d, d > 1 -> d < i -> ~divisible d p).

Arguments modulo x y : simpl never.

Theorem prime_check_correct: forall (n: nat) (POS: n > 2),
  {{ N = n }} 
    prime_check_com
  {{ (RES = 1) <-> prime n }}.
Proof.
  intros. unfold prime_check_com.
  hauto.
  - hauto_while (fun st => st N = n /\ st I >= 3 /\ st I <= st N /\ (exists k, st I = 1 + 2*k) /\ (st RES = 1 <-> indivisible_upto (st I) (st N))).
    + hauto_vc. split; hauto_vc.
      * split; intros. { destruct H3 as [k ?]. exists (k+1). nia. }
        split; intros; try nia.
        destruct H8. hexploit (H9 (st I)); try nia; intros.
        exfalso. apply H10.
        exists (st N / st I). nia.
      * split; intros. { destruct H3 as [k ?]. exists (k+1). nia. }
        repeat (split; intros; try nia).
        assert (CASE: d < st I \/ d = st I \/ d = st I + 1) by nia.
        destruct CASE as [CASE1 | [CASE2 | CASE3]].
        -- eapply H4; try nia.
        -- intros [q EQ]. subst.
           hexploit (mod_mul q (st I)); try nia.
           rewrite mul_comm, <-EQ; nia.
        -- intros [q EQ]. subst.
           eapply H4 in H5. destruct H5.
           hexploit (H11 2); try nia.
           intros. apply H12.
           destruct H3 as [k ?].
           exists ((k+1)*q). nia.
    + hauto_vc. destruct H0; cycle 1.
      * hauto_vc. apply H4.
        destruct H0. split; eauto.
        red; intros. apply H5 in H8. nia.
      * split; intros.
        -- apply H4 in H0.
           split; try nia.
           intros. destruct H0.
           destruct DIV.
           assert ((d = 1 \/ d = st N) \/ (d > 1 /\ d < st I) \/ (d <> st N /\ d >= st I)) by nia.
           destruct H7 as [C1 | [C2 | C3]].
           ++ nia.
           ++ assert (INDIV := H5 d). red in INDIV.
              hexploit INDIV; try nia.
              exists x; nia.
           ++ destruct C3.
              assert (x <> 1 /\ x < st I) by nia.
              assert (INDIV := H5 x). red in INDIV.
              hexploit INDIV; try nia.
              exists d. nia.
        -- apply H4.
           destruct H0. split; eauto.
           red; intros. apply H5 in H8. nia.
  - hauto_vc. split; intros.
    + hauto_vc. destruct H2. specialize (H3 2). 
      hexploit H3; try nia.
      exists (st N /2); nia.
    + hauto_vc. split.
      * exists 1. nia.
      * split; intros; eauto.
        split; try nia.
        red; intros. destruct H5. nia.
Qed.

