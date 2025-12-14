(** Final Exam *)

Set Warnings "-notation-overridden,-parsing".
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Init.Nat.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Arith.PeanoNat. Import Nat.
From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List. Import ListNotations.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Relations.
From Stdlib Require Import Logic.FunctionalExtensionality.

Require Import Program Program.Wf Permutation.

(* ################################################################# *)
(** * evar_at_last_[i] *)

(* evar_at_last_[i] makes the [i]th argument from the end as an evar. *)

Ltac evar_at_last_1 :=
  match goal with [|- _ ?arg] => pattern arg end; eapply eq_ind.
Ltac evar_at_last_2 :=
  match goal with [|- _ ?arg _] => pattern arg end; eapply eq_ind.
Ltac evar_at_last_3 :=
  match goal with [|- _ ?arg _ _] => pattern arg end; eapply eq_ind.
Ltac evar_at_last_4 :=
  match goal with [|- _ ?arg _ _ _] => pattern arg end; eapply eq_ind.
Ltac evar_at_last_5 :=
  match goal with [|- _ ?arg _ _ _ _] => pattern arg end; eapply eq_ind.
Ltac evar_at_last_6 :=
  match goal with [|- _ ?arg _ _ _ _ _] => pattern arg end; eapply eq_ind.
Ltac evar_at_last_7 :=
  match goal with [|- _ ?arg _ _ _ _ _ _] => pattern arg end; eapply eq_ind.
Ltac evar_at_last_8 :=
  match goal with [|- _ ?arg _ _ _ _ _ _ _] => pattern arg end; eapply eq_ind.
Ltac evar_at_last_9 :=
  match goal with [|- _ ?arg _ _ _ _ _ _ _ _] => pattern arg end; eapply eq_ind.

(* ################################################################# *)
(** * hexploit *)

(* [hexploit]: A very useful tactic, developed by Gil Hur.

   Suppose we have:

     H: P1 -> ... -> Pn -> Q
     ========================
     G

   [hexploit H] turns this goal into the following (n+1) subgoals:

     H: P1 -> ... -> Pn -> Q
     =========================
     P1

     ...

     H: P1 -> ... -> Pn -> Q
     =========================
     Pn

     H: P1 -> ... -> Pn -> Q
     =========================
     Q -> G
*)

Lemma __mp__: forall P Q: Type, P -> (P -> Q) -> Q.
Proof. intuition. Defined.

Ltac hexploit H := eapply __mp__; [eapply H|].

(* ################################################################# *)
(** * revert_until *)

Ltac on_last_hyp tac :=
  match goal with [ H : _ |- _ ] => first [ tac H | fail 1 ] end.

Ltac revert_until id :=
  on_last_hyp ltac:(fun id' =>
    match id' with
      | id => idtac
      | _ => revert id' ; revert_until id
    end).

(** ############################################################### **)
(**                                                                 **)
(**                               Maps                              **)
(**                                                                 **)
(** ############################################################### **)

(** * Total Maps *)

Definition total_map (A : Type) := string -> A.

Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if String.eqb x x' then v else m x'.

Definition examplemap :=
  t_update (t_update (t_empty false) "foo" true)
           "bar" true.

Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).

Example example_empty := (_ !-> false).

Notation "x '!->' v ';' m" := (t_update m x v)
                                (at level 100, x constr, right associativity).

Definition examplemap' :=
  ( "bar" !-> true;
    "foo" !-> true;
    _     !-> false
  ).

Example update_example1 : examplemap' "baz" = false.
Proof. reflexivity. Qed.

Example update_example2 : examplemap' "foo" = true.
Proof. reflexivity. Qed.

Example update_example3 : examplemap' "quux" = false.
Proof. reflexivity. Qed.

Example update_example4 : examplemap' "bar" = true.
Proof. reflexivity. Qed.

Lemma t_apply_empty : forall (A : Type) (x : string) (v : A),
  (_ !-> v) x = v.
Proof. eauto. Qed.
(** [] *)

Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
  (x !-> v ; m) x = v.
Proof.
  intros. unfold t_update. rewrite eqb_refl. eauto.
Qed.

Theorem t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
  x1 <> x2 ->
  (x1 !-> v ; m) x2 = m x2.
Proof.
  intros. unfold t_update. erewrite (proj2 (eqb_neq _ _)); eauto.
Qed.

Lemma t_update_shadow : forall (A : Type) (m : total_map A) x v1 v2,
  (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof.
  intros. apply functional_extensionality. intros.
  unfold t_update. destruct (x =? x0)%string; eauto.
Qed.

Theorem t_update_same : forall (A : Type) (m : total_map A) x,
  (x !-> m x ; m) = m.
Proof.
  intros. apply functional_extensionality. intros.
  unfold t_update. destruct (_ =? _)%string eqn: EQ; eauto.
  eapply eqb_eq in EQ. subst. eauto.
Qed.

Theorem t_update_permute : forall (A : Type) (m : total_map A)
                                  v1 v2 x1 x2,
  x2 <> x1 ->
  (x1 !-> v1 ; x2 !-> v2 ; m)
  =
  (x2 !-> v2 ; x1 !-> v1 ; m).
Proof.
  intros. apply functional_extensionality. intros.
  unfold t_update.
  destruct (x1 =? x)%string eqn: EQ1; eauto.
  destruct (x2 =? x)%string eqn: EQ2; eauto.
  eapply eqb_eq in EQ1.
  eapply eqb_eq in EQ2.
  subst. contradiction.
Qed.

(* ################################################################# *)
(** * Partial maps *)

Definition partial_map (A : Type) := total_map (option A).

Definition empty {A : Type} : partial_map A :=
  t_empty None.

Definition update {A : Type} (m : partial_map A)
           (x : string) (v : A) :=
  (x !-> Some v ; m).

Notation "x '|->' v ';' m" := (update m x v)
  (at level 0, x constr, v at level 200, right associativity).

Notation "x '|->' v" := (update empty x v)
  (at level 0, x constr, v at level 200).

Definition examplepmap :=
  ("Church" |-> true ; "Turing" |-> false).

Lemma apply_empty : forall (A : Type) (x : string),
  @empty A x = None.
Proof.
  intros. unfold empty. rewrite t_apply_empty.
  reflexivity.
Qed.

Lemma update_eq : forall (A : Type) (m : partial_map A) x v,
  (x |-> v ; m) x = Some v.
Proof.
  intros. unfold update. rewrite t_update_eq.
  reflexivity.
Qed.

#[global] Hint Resolve update_eq : core.

Theorem update_neq : forall (A : Type) (m : partial_map A) x1 x2 v,
  x2 <> x1 ->
  (x2 |-> v ; m) x1 = m x1.
Proof.
  intros A m x1 x2 v H.
  unfold update. rewrite t_update_neq.
  - reflexivity.
  - apply H.
Qed.

Lemma update_shadow : forall (A : Type) (m : partial_map A) x v1 v2,
  (x |-> v2 ; x |-> v1 ; m) = (x |-> v2 ; m).
Proof.
  intros A m x v1 v2. unfold update. rewrite t_update_shadow.
  reflexivity.
Qed.

Theorem update_same : forall (A : Type) (m : partial_map A) x v,
  m x = Some v ->
  (x |-> v ; m) = m.
Proof.
  intros A m x v H. unfold update. rewrite <- H.
  apply t_update_same.
Qed.

Theorem update_permute : forall (A : Type) (m : partial_map A)
                                x1 x2 v1 v2,
  x2 <> x1 ->
  (x1 |-> v1 ; x2 |-> v2 ; m) = (x2 |-> v2 ; x1 |-> v1 ; m).
Proof.
  intros A m x1 x2 v1 v2. unfold update.
  apply t_update_permute.
Qed.

Definition includedin {A : Type} (m m' : partial_map A) :=
  forall x v, m x = Some v -> m' x = Some v.

Lemma includedin_update : forall (A : Type) (m m' : partial_map A)
                                 (x : string) (vx : A),
  includedin m m' ->
  includedin (x |-> vx ; m) (x |-> vx ; m').
Proof.
  unfold includedin.
  intros A m m' x vx H.
  intros y vy.
  destruct (eqb_spec x y) as [Hxy | Hxy].
  - rewrite Hxy.
    rewrite update_eq. rewrite update_eq. intro H1. apply H1.
  - rewrite update_neq.
    + rewrite update_neq.
      * apply H.
      * apply Hxy.
    + apply Hxy.
Qed.

(** ############################################################### **)
(**                                                                 **)
(** *                             Array                             **)
(**                                                                 **)
(** ############################################################### **)

(****
  Pair encoding
 ****)

Definition nat2bool (n: nat) : bool :=
  match n mod 2 with
  | 0 => false
  | _ => true
  end.

Definition bool2nat (b: bool) : nat :=
  match b with
  | false => 0
  | true => 1
  end.

Program Fixpoint nat2bits (n: nat) {measure n} : list bool :=
  match n with
  | 0 => []
  | _ => nat2bool n :: nat2bits (n/2)
  end.
Next Obligation.
  destruct (divmod n 1 0 1) eqn: EQ. simpl.
  assert (SPEC:= divmod_spec n 1 0 1).
  rewrite EQ in SPEC. nia.
Qed.

Fixpoint bits2nat (bs: list bool) : nat :=
  match bs with
  | [] => 0
  | b :: bs' => bool2nat b + bits2nat bs' * 2
  end.

Fixpoint zip_nil_with_bits (bs: list bool) : list bool :=
  match bs with
  | [] => []
  | b :: bs' => false :: b :: zip_nil_with_bits bs'
  end.

Fixpoint zip_bits (bs1 bs2: list bool) : list bool :=
  match bs1 with
  | [] => zip_nil_with_bits bs2
  | b1 :: bs1' =>
      match bs2 with
      | [] => b1 :: false :: zip_bits bs1' []
      | b2 :: bs2' => b1 :: b2 :: zip_bits bs1' bs2'
      end
  end.

Fixpoint unzip_bits (bs: list bool) : list bool * list bool :=
  match bs with
  | [] => ([], [])
  | b :: [] => ([b], [false])
  | b1 :: b2 :: bs' =>
      let (bs1, bs2) := unzip_bits bs' in
      (b1 :: bs1, b2 :: bs2)
  end.

Definition encode_pair (n m: nat) : nat :=
  bits2nat (zip_bits (nat2bits n) (nat2bits m)).

Definition decode_pair (n: nat) : nat * nat :=
  let (bs1, bs2) := unzip_bits (nat2bits n) in
  (bits2nat bs1, bits2nat bs2).

Definition bprefix (bs bs': list bool) : Prop :=
  exists n, bs' = bs ++ repeat false n.

(* Properties *)

Lemma nat2bool_bool2nat n:
  bool2nat (nat2bool n) = n mod 2.
Proof.
  unfold nat2bool, bool2nat.
  destruct (n mod 2) eqn: EQ; eauto.
  hexploit (mod_upper_bound n 2); eauto. nia.
Qed.

Lemma bool2nat_nat2bool b:
  nat2bool (bool2nat b) = b.
Proof.
  unfold nat2bool, bool2nat. destruct b; eauto.
Qed.

Lemma nat2bits_unfold n:
  nat2bits n = match n with
               | 0 => []
               | _ => nat2bool n :: nat2bits (n/2)
               end.
Proof.
  unfold nat2bits. rewrite Fix_eq.
  - destruct n; simpl; eauto.
  - intros. destruct x; eauto. rewrite H. eauto.
Qed.

Lemma nat2bits_step_0:
  nat2bits 0 = [].
Proof. rewrite nat2bits_unfold. eauto. Qed.

Lemma nat2bits_step_1:
  nat2bits 1 = [true].
Proof. rewrite nat2bits_unfold. eauto. Qed.

Lemma nat2bits_step q r
  (NZ: q > 0)
  (RES: r <= 1)
  :
  nat2bits (r + q * 2) = nat2bool r :: nat2bits q.
Proof.
  rewrite nat2bits_unfold.
  destruct (r + q * 2) eqn: EQ; try nia.
  f_equal.
  - unfold nat2bool. rewrite <-EQ, Div0.mod_add. eauto.
  - rewrite nat2bits_unfold, (nat2bits_unfold q). 
    erewrite <-(div_unique _ _ q r); try nia. eauto.
Qed.

Lemma nat2bits_zero bs
  (ZERO: bits2nat bs = 0)
  :
  bs = repeat false (List.length bs).
Proof.
  revert_until bs. induction bs; eauto.
  intros. destruct a; simpl in ZERO; try nia.
  hexploit IHbs; try nia. intros.
  simpl. f_equal. eauto.
Qed.

Lemma bits2nat_zeros n :
  bits2nat (repeat false n) = 0.
Proof.
  intros. induction n; simpl; nia.
Qed.

Lemma zip_bits_repeat_false n1 n2 :
  exists n, zip_bits (repeat false n1) (repeat false n2) = repeat false n.
Proof.
  revert n2. induction n1; intros.
  { induction n2.
    - exists 0. eauto.
    - destruct IHn2. exists (S (S x)). simpl. rewrite <-H. eauto.
  }
  destruct n2.
  - edestruct (IHn1 0). exists (S (S x)). simpl. rewrite <-H. eauto.
  - edestruct (IHn1 n2). exists (S (S x)). simpl. rewrite <-H. eauto.
Qed.

Lemma zip_bits_bprefix bs1 bs2 bs1' bs2'
  (PREF1: bprefix bs1 bs1')
  (PREF2: bprefix bs2 bs2')
  :
  bprefix (zip_bits bs1 bs2) (zip_bits bs1' bs2').
Proof.
  destruct PREF1, PREF2. subst.
  revert_until bs1. induction bs1; intros.
  { revert_until bs2. induction bs2; simpl; intros.
    - destruct (zip_bits_repeat_false x x0). exists x1. eauto.
    - destruct (IHbs2 (pred x) x0). exists x1. simpl in *. rewrite <-H.
      destruct x; eauto.
  }

  destruct bs2.
  { destruct (IHbs1 [] x (pred x0)). simpl in H. exists x1. simpl. rewrite <-H.
    destruct x0; eauto.
  }

  destruct (IHbs1 bs2 x x0). exists x1. simpl. rewrite <-H. eauto.
Qed.

Lemma bprefix_bits2nat bs bs'
  (LE: bprefix bs bs')
  :
  bits2nat bs = bits2nat bs'.
Proof.
  revert_until bs. induction bs; intros.
  - destruct LE. subst. simpl. rewrite bits2nat_zeros. eauto.
  - destruct LE. subst. simpl.
    hexploit (IHbs (bs ++ repeat false x)).
    { red; eauto. }
    intros. nia.
Qed.

Lemma bprefix_refl bs:
  bprefix bs bs.
Proof.
  exists 0. simpl. rewrite List.app_nil_r. eauto.
Qed.

Lemma nat2bits_bits2nat n :
  n = bits2nat (nat2bits n).
Proof.
  cut (forall m (LE: m <= n), m = bits2nat (nat2bits m)).
  { eauto. }
  induction n; intros.
  { destruct m; simpl; nia. }
  destruct m; eauto.
  assert (DIV := Div0.div_mod (S m) 2).
  hexploit (IHn (S m / 2)); try nia. intros.
  rewrite nat2bits_unfold.
  unfold bits2nat. fold bits2nat.
  rewrite nat2bool_bool2nat. nia.
Qed.

Lemma bits2nat_nat2bits bs :
  bprefix (nat2bits (bits2nat bs)) bs.
Proof.
  induction bs.
  { exists 0. eauto. }
  destruct IHbs.

  destruct (bits2nat bs) eqn: EQ.
  { simpl bits2nat. rewrite EQ. simpl. destruct a.
    - simpl. rewrite nat2bits_step_1. exists (List.length bs). simpl. f_equal.
      eapply nat2bits_zero in EQ. eauto.
    - simpl. rewrite nat2bits_step_0. exists (1 + List.length bs). simpl. f_equal.
      eapply nat2bits_zero in EQ. eauto.
  }
  simpl bits2nat. rewrite nat2bits_step; try nia; cycle 1.
  { destruct a; simpl; nia. }
  rewrite bool2nat_nat2bool. rewrite H at 2. rewrite EQ. exists x. eauto.
Qed.

Lemma unzip_zip_bits bs bs1 bs2 bs'
  (PREF1: bprefix bs1 (fst (unzip_bits bs)))
  (PREF2: bprefix bs2 (snd (unzip_bits bs)))
  (ZIP: bs' = zip_bits bs1 bs2)
  :
  bits2nat bs' = bits2nat bs.
Proof.
  revert_until bs.
  cut (forall bs0 bs' bs1 bs2 (PAT: bs0 = bs \/ bs0 = tail bs)
              (PREF1: bprefix bs1 (fst (unzip_bits bs0)))
              (PREF2: bprefix bs2 (snd (unzip_bits bs0)))
              (ZIP: bs' = zip_bits bs1 bs2),
          bits2nat bs' = bits2nat bs0); eauto.
  
  induction bs; intros; destruct PREF1, PREF2.
  { destruct PAT; subst; simpl in *; destruct bs1, bs2; eauto; discriminate. }
  
  destruct bs.
  { destruct PAT; subst; simpl in *; cycle 1.
    { destruct bs1, bs2; eauto; discriminate. }
    destruct a, bs1, bs2; try destruct x; try destruct b; try destruct b0;
      try destruct bs1; try destruct bs2; eauto; discriminate.
  }
    
  destruct PAT; subst; cycle 1.
  { eapply IHbs; try eexists; eauto. }

  simpl in H, H0. destruct (unzip_bits bs) as [bs1' bs2'] eqn: EQ. simpl in H, H0.
  hexploit IHbs; try right; eauto using bprefix_refl.
  simpl. rewrite EQ. simpl. intros UZ. rewrite <-UZ.
  
  erewrite bprefix_bits2nat; cycle 1.
  - eapply zip_bits_bprefix; [exists x|exists x0]; eauto.
  - eauto.
Qed.

Lemma zip_bits_bprefix_nil bs1 bs2
  (RF: bprefix [] (zip_bits bs1 bs2))
  :
  bprefix [] bs1 /\ bprefix [] bs2.
Proof.
  destruct RF. revert bs1 bs2 H. simpl.
  cut (forall x0 bs1 bs2 (RF: zip_bits bs1 bs2 = repeat false x0) (LE: x0 <= x),
          bprefix [] bs1 /\ bprefix [] bs2); eauto.
  induction x; intros.
  - destruct x0; try nia.
    destruct bs1, bs2; inversion RF. split; exists 0; eauto.
  - destruct (IHx (pred (pred x0)) (tl bs1) (tl bs2)); try nia.
    + destruct bs1, bs2, x0; dependent destruction RF; subst; simpl; eauto;
        destruct x0; inversion x; eauto.
    + destruct H, H0. split; red.
      * destruct bs1; simpl in *; subst; eauto.
        destruct b; [|exists (S x1); eauto]. destruct bs2, x0; discriminate.
      * destruct bs2; simpl in *; subst; eauto.
        destruct b; [|exists (S x2); eauto].
        destruct bs1, x0; try discriminate; destruct x0; discriminate.
Qed.
  
Lemma zip_unzip_bits bs bs1 bs2 bs1' bs2'
  (PREF: bprefix bs (zip_bits bs1 bs2))
  (ZU: (bs1', bs2') = unzip_bits bs)
  :
  bits2nat bs1' = bits2nat bs1 /\ bits2nat bs2' = bits2nat bs2.
Proof.
  destruct PREF. revert_until bs.
  cut (forall bs0 bs1 bs2 bs1' bs2' x (PAT: bs0 = bs \/ bs0 = tail bs)
              (PREF: zip_bits bs1 bs2 = bs0 ++ repeat false x)
              (UNZIP: (bs1',bs2') = unzip_bits bs0),
          bits2nat bs1' = bits2nat bs1 /\ bits2nat bs2' = bits2nat bs2); eauto.

  induction bs; intros.
  { destruct bs0; [clear PAT|destruct PAT; discriminate].
    inversion UNZIP; subst. simpl in *.
    edestruct zip_bits_bprefix_nil; [red; eauto|].
    erewrite <-(bprefix_bits2nat [] bs1); eauto.
    erewrite <-(bprefix_bits2nat [] bs2); eauto.
  }

  destruct PAT; subst; cycle 1.
  { edestruct IHbs; try left; eauto. }

  destruct bs; inversion UNZIP; subst; clear UNZIP.
  { edestruct (IHbs [] (tl bs1) (tl bs2) [] [] (pred x)); eauto.
    - destruct bs1, bs2, x; inversion PREF; subst; simpl in *; eauto.
    - destruct bs1, bs2, x; inversion PREF; subst; simpl in *; nia.
  }      

  destruct (unzip_bits bs) as [bs1u bs2u] eqn: EQ. inversion H0; subst; clear H0.
  edestruct (IHbs bs (tl bs1) (tl bs2) bs1u bs2u x); eauto.
  - destruct bs1, bs2; inversion PREF; eauto.
  - destruct bs1, bs2; inversion PREF; simpl in *; nia.
Qed.

Theorem dec_enc_correct: forall i n m (DEC: decode_pair i = (n,m)),
    encode_pair n m = i.
Proof.
  unfold encode_pair, decode_pair. intros.
  edestruct (unzip_bits _) eqn: EQ. inversion DEC; subst.
  rewrite (nat2bits_bits2nat i).
  eapply unzip_zip_bits; eauto; rewrite EQ; simpl; apply bits2nat_nat2bits.
Qed.

Theorem enc_dec_correct: forall n m, decode_pair (encode_pair n m) = (n, m).
Proof.
  unfold encode_pair, decode_pair. intros.
  edestruct (unzip_bits _) eqn: EQ.
  rewrite (nat2bits_bits2nat n), (nat2bits_bits2nat m).
  edestruct zip_unzip_bits; cycle 1.
  - symmetry. apply EQ.
  - f_equal; [apply H|apply H0].
  - apply bits2nat_nat2bits.
Qed.

(****
  Array encoding
 ****)

Fixpoint array_get (a i : nat) : nat :=
  match i with
  | 0 => fst (decode_pair a)
  | S i' => array_get (snd (decode_pair a)) i'
  end.

Fixpoint array_set (a i v : nat) : nat :=
  match i with
  | 0 => encode_pair v (snd (decode_pair a))
  | S i' => let (hd, tl) := decode_pair a in
            encode_pair hd (array_set tl i' v)
  end.

Fixpoint arr2list (arr: nat) (sz: nat) : list nat :=
  match sz with
  | 0 => []
  | S sz' => let (hd, tl) := decode_pair arr in
             hd :: arr2list tl sz'
  end.

Fixpoint set_nth {A : Type} (n : nat) (x : A) (l : list A) : list A :=
  match l, n with
  | [], _ => []
  | _ :: t, O => x :: t
  | h :: t, S n' => h :: set_nth n' x t
  end.

(* Properties *)

Lemma arr2list_get sz i arr
  (RANGE: i < sz)
  :
  array_get arr i = nth i (arr2list arr sz) 0.
Proof.
  move i at top. revert_until i; induction i; simpl; intros.
  - destruct sz; try nia. simpl.
    destruct (decode_pair arr). eauto.
  - destruct sz; try nia. simpl.
    destruct (decode_pair arr). simpl. eapply IHi. nia.
Qed.

Lemma arr2list_set sz i v arr
  (RANGE: i < sz)
  :
  arr2list (array_set arr i v) sz = set_nth i v (arr2list arr sz).
Proof.
  move i at top. revert_until i; induction i; simpl; intros.
  - destruct sz; try nia. simpl.
    destruct (decode_pair arr). rewrite enc_dec_correct. eauto.
  - destruct sz; try nia. simpl.
    destruct (decode_pair arr). rewrite enc_dec_correct.
    f_equal. eapply IHi. nia.
Qed.

Lemma arr2list_length arr sz:
  List.length (arr2list arr sz) = sz.
Proof.
  revert arr; induction sz; intros; eauto.
  simpl. destruct (decode_pair arr) eqn: EQ.
  simpl. rewrite IHsz. eauto.
Qed.

Lemma arr2list_plus_one sz arr:
  arr2list arr (sz + 1) = arr2list arr sz ++ [array_get arr sz].
Proof.
  revert_until sz. induction sz; simpl; intros; edestruct (decode_pair _); eauto.
  rewrite IHsz. eauto.
Qed.

Lemma get_set_nth_eq i v l
  (RANGE: i < List.length l)
  :
  nth i (set_nth i v l) 0 = v.
Proof.
  revert_until i. induction i; intros.
  - destruct l; simpl in *; try nia.
  - destruct l; simpl in *; try nia.
    eapply IHi. nia.
Qed.
                     
Lemma get_set_nth_neq i k v l
  (RANGE: i < List.length l)
  (NEQ: i <> k)
  :
  nth i (set_nth k v l) 0 = nth i l 0.
Proof.
  revert_until i. induction i; intros.
  - destruct l, k; simpl in *; try nia.
  - destruct l, k; simpl in *; try nia.
    eapply IHi; try nia.
Qed.

Lemma set_nth_length k v (l: list nat):
  List.length (set_nth k v l) = List.length l.
Proof.
  revert_until k. induction k; intros.
  - destruct l; eauto.
  - destruct l; eauto. simpl. rewrite IHk; eauto.
Qed.

Lemma set_nth_spec {T} k (v: T) l1 l2 v'
  (LEN: List.length l1 = k)
  :
  set_nth k v (l1 ++ [v'] ++ l2) = l1 ++ [v] ++ l2.
Proof.
  revert_until k. induction k; intros.
  - destruct l1; simpl in *; eauto. nia.
  - destruct l1; simpl in *; try nia.
    rewrite IHk; try nia. eauto.
Qed.

(** ############################################################### **)
(**                                                                 **)
(** *             Imp: Simple Imperative Programs                   **)
(**                                                                 **)
(** ############################################################### **)

Definition state := total_map nat.

(* ================================================================= *)
(** ** Syntax  *)

Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
  | AGet (a1 a2: aexp)
  | ASet (a1 a2 a3: aexp)
.

Variant aexp_div : Type :=
  | AExp (a: aexp)
  | ADiv (a1 a2 : aexp)
.

Coercion AExp: aexp >-> aexp_div.

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BNeq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BGt (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

(* ================================================================= *)
(** ** Notations *)

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.

Declare Custom Entry com.
Declare Scope com_scope.
Declare Custom Entry com_aux.

Notation "<{ e }>" := e (e custom com_aux) : com_scope.
Notation "e" := e (in custom com_aux at level 0, e custom com) : com_scope.

Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.

Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 1,
                      y constr at level 1) : com_scope.
Notation "x + y"   := (APlus x y) (in custom com at level 50, left associativity).
Notation "x - y"   := (AMinus x y) (in custom com at level 50, left associativity).
Notation "x * y"   := (AMult x y) (in custom com at level 40, left associativity).
Notation "x / y"   := (ADiv x y) (in custom com at level 40, left associativity).
Notation "a @ i" := (AGet a i) (in custom com at level 40, left associativity).
Notation "a '<|' i '~>' v '|>'" := (ASet a i v) (in custom com at level 40, left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := BTrue (in custom com at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := BFalse (in custom com at level 0).
Notation "x <= y"  := (BLe x y) (in custom com at level 70, no associativity).
Notation "x > y"   := (BGt x y) (in custom com at level 70, no associativity).
Notation "x = y"   := (BEq x y) (in custom com at level 70, no associativity).
Notation "x <> y"  := (BNeq x y) (in custom com at level 70, no associativity).
Notation "x && y"  := (BAnd x y) (in custom com at level 80, left associativity).
Notation "'~' b"   := (BNot b) (in custom com at level 75, right associativity).

Notation "x < y"   := (BGt y x) (in custom com at level 70, no associativity).
Notation "x >= y"  := (BLe y x) (in custom com at level 70, no associativity).
Notation "x || y"  := (BNot (BAnd (BNot x) (BNot y))) (in custom com at level 70, no associativity).

Open Scope com_scope.

(* ================================================================= *)
(** ** Evaluation *)

(** The arith and boolean evaluators must now be extended to
    handle variables in the obvious way, taking a state [st] as an
    extra argument: *)

Fixpoint aeval (st : state)
               (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x
  | <{a1 + a2}> => (aeval st a1) + (aeval st a2)
  | <{a1 - a2}> => (aeval st a1) - (aeval st a2)
  | <{a1 * a2}> => (aeval st a1) * (aeval st a2)
  | <{ a @ i }> => array_get (aeval st a) (aeval st i)
  | <{ a <| i ~> v |> }> => array_set (aeval st a) (aeval st i) (aeval st v)
  end.

Definition aeval_div st a : nat :=
  match a with
  | AExp a0 => aeval st a0
  | ADiv a1 a2 => aeval st a1 / aeval st a2
  end.

Definition aeval_div_error st a : Prop :=
  match a with
  | AExp _ => False
  | ADiv a1 a2 => aeval st a2 = 0
  end.

Fixpoint beval (st : state)
               (b : bexp) : bool :=
  match b with
  | <{true}>      => true
  | <{false}>     => false
  | <{a1 = a2}>   => (aeval st a1) =? (aeval st a2)
  | <{a1 <> a2}>  => negb ((aeval st a1) =? (aeval st a2))
  | <{a1 <= a2}>  => (aeval st a1) <=? (aeval st a2)
  | <{a1 > a2}>   => negb ((aeval st a1) <=? (aeval st a2))
  | <{~ b1}>      => negb (beval st b1)
  | <{b1 && b2}>  => andb (beval st b1) (beval st b2)
  end.

Definition empty_st := (_ !-> 0).

Notation "x '!->' v" := (x !-> v ; empty_st) (at level 100, v at level 200).

(* ################################################################# *)
(** * Commands *)

(* ================================================================= *)
(** ** Syntax *)

Inductive com : Type :=
  | CSkip
  | CAsgn (x : string) (a : aexp_div)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

Notation "'skip'"  :=
         CSkip (in custom com at level 0) : com_scope.
Notation "x := y"  :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
                y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90,
            right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
           (in custom com at level 89, x at level 99,
            y at level 99) : com_scope.

Reserved Notation
         "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).

Inductive ceval : com -> state -> option state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> Some st
  | E_Asgn  : forall st a n x,
      ~ aeval_div_error st a ->  
      aeval_div st a = n ->
      st =[ x := a ]=> Some (x !-> n ; st)
  | E_Asgn_Error : forall st a x,
      aeval_div_error st a ->
      st =[ x := a ]=> None
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> Some st'  ->
      st' =[ c2 ]=> Some st'' ->
      st  =[ c1 ; c2 ]=> Some st''
  | E_Seq_Error1 : forall c1 c2 st,
      st  =[ c1 ]=> None ->
      st  =[ c1 ; c2 ]=> None
  | E_Seq_Error2 : forall c1 c2 st st',
      st  =[ c1 ]=> Some st'  ->
      st' =[ c2 ]=> None ->
      st  =[ c1 ; c2 ]=> None
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> Some st' ->
      st =[ if b then c1 else c2 end]=> Some st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> Some st' ->
      st =[ if b then c1 else c2 end]=> Some st'
  | E_IfTrue_Error : forall st b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> None ->
      st =[ if b then c1 else c2 end]=> None
  | E_IfFalse_Error : forall st b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> None ->
      st =[ if b then c1 else c2 end]=> None
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> Some st' ->
      st' =[ while b do c end ]=> Some st'' ->
      st  =[ while b do c end ]=> Some st''
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> Some st
  | E_WhileTrue_Error1 : forall st b c,
      beval st b = true ->
      st  =[ c ]=> None ->
      st  =[ while b do c end ]=> None
  | E_WhileTrue_Error2 : forall st st' b c,
      beval st b = true ->
      st  =[ c ]=> Some st' ->
      st' =[ while b do c end ]=> None ->
      st  =[ while b do c end ]=> None

  where "st =[ c ]=> st'" := (ceval c st st').

(* Tactics for executing [ceval]. *)

Ltac ceval_step :=
  first [eapply E_Seq|eapply E_Skip|eapply E_Asgn|eapply E_IfTrue|eapply E_IfFalse|eapply E_WhileTrue]; eauto.

Ltac ceval_steps :=
  repeat (ceval_step; simpl; try match goal with [|- false = true] => fail 2 end);
  eauto using ceval.

(** ############################################################### **)
(**                                                                 **)
(** *                        Hoare Logic                            **)
(**                                                                 **)
(** ############################################################### **)

(* ################################################################# *)
(** * Assertions *)

Definition Assertion := state -> Prop.

Definition Aexp : Type := state -> nat.

Definition assert_of_Prop (P : Prop) : Assertion := fun _ => P.
Definition Aexp_of_nat (n : nat) : Aexp := fun _ => n.

Definition Aexp_of_aexp (a : aexp_div) : Aexp := fun st => aeval_div st a.

Coercion assert_of_Prop : Sortclass >-> Assertion.
Coercion Aexp_of_nat : nat >-> Aexp.
Coercion Aexp_of_aexp : aexp_div >-> Aexp.

Arguments assert_of_Prop /.
Arguments Aexp_of_nat /.
Arguments Aexp_of_aexp /.

Declare Custom Entry assn. (* The grammar for Hoare logic Assertions *)
Declare Scope assertion_scope.
Bind Scope assertion_scope with Assertion.
Bind Scope assertion_scope with Aexp.
Delimit Scope assertion_scope with assertion.

Notation "# f x .. y" := (fun (st: state) => (.. (f ((x:Aexp) st)) .. ((y:Aexp) st)))
                  (in custom assn at level 2,
                  f constr at level 0, x custom assn at level 1,
                  y custom assn at level 1) : assertion_scope.

Notation "P -> Q" := (fun (st: state) => (P:Assertion) st -> (Q:Assertion) st) (in custom assn at level 99, right associativity) : assertion_scope.
Notation "P <-> Q" := (fun (st: state) => (P:Assertion) st <-> (Q:Assertion) st) (in custom assn at level 95) : assertion_scope.

Notation "P \/ Q" := (fun (st: state) => (P:Assertion) st \/ (Q:Assertion) st) (in custom assn at level 85, right associativity) : assertion_scope.
Notation "P /\ Q" := (fun (st: state) => (P:Assertion) st /\ (Q:Assertion) st) (in custom assn at level 80, right associativity) : assertion_scope.
Notation "~ P" := (fun (st: state) => ~ ((P:Assertion) st)) (in custom assn at level 75, right associativity) : assertion_scope.
Notation "a = b" := (fun (st: state) => (a:Aexp) st = (b:Aexp) st) (in custom assn at level 70) : assertion_scope.
Notation "a <> b" := (fun (st: state) => (a:Aexp) st <> (b:Aexp) st) (in custom assn at level 70) : assertion_scope.
Notation "a <= b" := (fun (st: state) => (a:Aexp) st <= (b:Aexp) st) (in custom assn at level 70) : assertion_scope.
Notation "a < b" := (fun (st: state) => (a:Aexp) st < (b:Aexp) st) (in custom assn at level 70) : assertion_scope.
Notation "a >= b" := (fun (st: state) => (a:Aexp) st >= (b:Aexp) st) (in custom assn at level 70) : assertion_scope.
Notation "a > b" := (fun (st: state) => (a:Aexp) st > (b:Aexp) st) (in custom assn at level 70) : assertion_scope.
Notation "'div_error' a" := (fun (st: state) => aeval_div_error st a) (in custom assn at level 0) : assertion_scope.
Notation "'True'" := True.
Notation "'True'" := (fun (st: state) => True) (in custom assn at level 0) : assertion_scope.
Notation "'False'" := False.
Notation "'False'" := (fun (st: state) => False) (in custom assn at level 0) : assertion_scope.

Notation "a + b" := (fun (st: state) => (a:Aexp) st + (b:Aexp) st) (in custom assn at level 50, left associativity) : assertion_scope.
Notation "a - b" := (fun (st: state) => (a:Aexp) st - (b:Aexp) st) (in custom assn at level 50, left associativity) : assertion_scope.
Notation "a * b" := (fun (st: state) => (a:Aexp) st * (b:Aexp) st) (in custom assn at level 40, left associativity) : assertion_scope.

Notation "( x )" := x (in custom assn at level 0, x at level 99) : assertion_scope.

Notation "$ f" := f (in custom assn at level 0, f constr at level 0) : assertion_scope.
Notation "x" := (x%assertion) (in custom assn at level 0, x constr at level 0) : assertion_scope.

Declare Scope hoare_spec_scope.
Open Scope hoare_spec_scope.

Notation "{{ e }}" := e (at level 2, e custom assn at level 99) : assertion_scope.
Open Scope assertion_scope.

(* ================================================================= *)
(** ** Assertion Implication *)

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Notation "P ->> Q" := (assert_implies P Q)
                        (at level 80) : hoare_spec_scope.

Notation "P <<->> Q" := (P ->> Q /\ Q ->> P)
                          (at level 80) : hoare_spec_scope.

(* ################################################################# *)
(** * Hoare Triples, Formally *)

Definition valid_hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st ost',
    st =[ c ]=> ost' ->
    P st  ->
    exists st', ost' = Some st' /\ Q st'.

Notation "{{ P }} c {{ Q }}" :=
  (valid_hoare_triple P c Q)
    (at level 2, P custom assn at level 99, c custom com at level 99, Q custom assn at level 99)
    : hoare_spec_scope.

(* ################################################################# *)
(** * Proof Rules *)

Theorem hoare_skip : forall P,
     {{P}} skip {{P}}.
Proof.
  intros P st st' H HP. inversion H; subst. eauto.
Qed.

Theorem hoare_seq : forall P Q R c1 c2,
     {{Q}} c2 {{R}} ->
     {{P}} c1 {{Q}} ->
     {{P}} c1; c2 {{R}}.
Proof.
  intros P Q R c1 c2 H1 H2 st st' H12 Pre.
  inversion H12; subst.
  - edestruct H2 as [st' [EQ HQ]]; eauto. inversion EQ; subst.
    edestruct H1 as [st''0 [EQ' Post]]; eauto.
  - edestruct H2 as [? [? ?]]; eauto. discriminate.
  - edestruct H2 as [st' [EQ HQ]]; eauto. inversion EQ; subst.
    edestruct H1 as [? [? ?]]; eauto.
Qed.

Definition assertion_sub X (a:aexp_div) (P:Assertion) : Assertion :=
  fun (st : state) =>
    P (X !-> ((a:Aexp) st); st).

Notation "P [ X |-> a ]" := (assertion_sub X a P)
                              (in custom assn at level 10, left associativity, P custom assn, X global, a custom com) : assertion_scope.

Theorem hoare_asgn : forall Q X (a:aexp),
  {{Q [X |-> a]}} X := a {{Q}}.
Proof.
  intros Q X a st st' HE HQ.
  inversion HE; subst; try firstorder.
Qed.

Theorem hoare_div : forall Q (X: string) (a1 a2: aexp),
  {{ a2 <> 0 /\
     (a1 = a2 * (#div a1 a2) + (#modulo a1 a2) -> (#modulo a1 a2) < a2 ->
      Q[X |-> a1 / a2]) }}
  X := a1 / a2
  {{ Q }}.
Proof.
  red; intros. destruct H0.
  inversion H; subst.
  - eexists. split; eauto.
    apply H1.
    + eapply div_mod; eauto.
    + eauto using mod_upper_bound.
   - simpl in *. nia.
Qed.

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  unfold valid_hoare_triple, "->>".
  intros P P' Q c Hhoare Himp st st' Heval Hpre.
  apply Hhoare with (st := st).
  - assumption.
  - apply Himp. assumption.
Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  unfold valid_hoare_triple, "->>".
  intros P Q Q' c Hhoare Himp st st' Heval Hpre.
  edestruct Hhoare as [st'0 [EQ Hpost]]; eauto.
Qed.

Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  {{P'}} c {{Q'}} ->
  P ->> P' ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q Q' c Htriple Hpre Hpost.
  apply hoare_consequence_pre with (P' := P').
  - apply hoare_consequence_post with (Q' := Q'); assumption.
  - assumption.
Qed.

Hint Unfold assert_implies assertion_sub t_update : core.
Hint Unfold valid_hoare_triple : core.
Hint Unfold assert_of_Prop Aexp_of_nat Aexp_of_aexp : core.

Definition bassertion b : Assertion :=
  fun st => (beval st b = true).

Coercion bassertion : bexp >-> Assertion.

Arguments bassertion /.

Lemma bexp_eval_false : forall b st,
  beval st b = false -> ~ ((bassertion b) st).
Proof. congruence. Qed.

Hint Resolve bexp_eval_false : core.

Theorem hoare_if : forall P Q (b:bexp) c1 c2,
  {{ P /\ b }} c1 {{Q}} ->
  {{ P /\ ~ b}} c2 {{Q}} ->
  {{P}} if b then c1 else c2 end {{Q}}.
Proof.
  intros P Q b c1 c2 HTrue HFalse st st' HE HP.
  inversion HE; subst; eauto.
Qed.

Theorem hoare_if_wp : forall P1 P2 Q (b:bexp) c1 c2,
    {{ P1 }} c1 {{ Q }} ->
    {{ P2 }} c2 {{ Q }} ->
    {{ (b -> P1) /\ (~ b -> P2) }} if b then c1 else c2 end {{ Q }}.
Proof.
  intros P1 P2 Q b c1 c2 HTrue HFalse st st' HE [HP1 HP2].
  inversion HE; subst; eauto.
Qed.

Theorem hoare_while : forall P (b:bexp) c,
  {{P /\ b}} c {{P}} ->
  {{P}} while b do c end {{P /\ ~ b}}.
Proof.
  intros P b c Hhoare st st' Heval HP.
  remember <{while b do c end}> as original_command eqn:Horig.
  induction Heval; intros;
    try (inversion Horig; subst); eauto.

  - edestruct Hhoare as [st'0 [EQ' HP']]; eauto. inversion EQ'; subst.
    edestruct IHHeval2 as [st''0 [EQ'' [HP'' Hcond]]]; eauto.
  - edestruct Hhoare as [? [? ?]]; eauto. discriminate.
  - edestruct Hhoare as [st'0 [EQ' HP']]; eauto. inversion EQ'; subst.
    edestruct IHHeval2 as [? [? ?]]; eauto.
Qed.

(* ################################################################# *)
(** * Automation for Hoare Logic *)

(******
   Automation based on Weakest Precondition
 ******)

Lemma assert_implies_refl (P: Assertion):
  P ->> P.
Proof.
  red; intros. eauto.
Qed.

Ltac hauto_vc :=
  eauto;
  unfold "->>", assertion_sub, t_update, bassertion;
  intros; simpl in *;
  repeat
    match goal with
    | [H: _ <> true |- _] => apply not_true_iff_false in H
    | [H: _ <> false |- _] => apply not_false_iff_true in H
    | [H: _ /\ _ |- _] => destruct H
    | [H: _ && _ = true |- _] => apply andb_true_iff in H
    | [H: _ && _ = false |- _] => apply andb_false_iff in H
    | [H: _ || _ = true |- _] => apply orb_true_iff in H
    | [H: _ || _ = false |- _] => apply orb_false_iff in H
    | [H: negb _ = true |- _] => eapply negb_true_iff in H
    | [H: negb _ = false |- _] => eapply negb_false_iff in H
    | [H: (_ =? _) = true |- _] => eapply Nat.eqb_eq in H
    | [H: (_ =? _) = false |- _] => eapply Nat.eqb_neq in H
    end;
  repeat (
    try rewrite -> Nat.eqb_eq in *;
    try rewrite leb_iff in *;
    try rewrite leb_iff_conv in *
  );
  try discriminate; try contradiction; eauto; subst; try nia;
  repeat (split; intros; [eauto; nia|]);
  intros; eauto.

Ltac hauto_split1 :=
  try match goal with
      | [|- {{_}} skip {{_}}] =>
        first [eapply hoare_skip; fail | eapply hoare_consequence_pre; [eapply hoare_skip|]]
      | [|- {{_}} _ := _ / _ {{_}}] =>
        first [eapply hoare_div;[] | eapply hoare_consequence_pre; [eapply hoare_div|]]
      | [|- {{_}} _ := _ {{_}}] =>
        first [eapply hoare_asgn;[] | eapply hoare_consequence_pre; [eapply hoare_asgn|]]
      | [|- {{_}} _; _ {{_}}] =>
        eapply hoare_seq
      | [|- {{_}} if _ then _ else _ end {{_}}] =>
        first [eapply hoare_if_wp;[|] | eapply hoare_consequence_pre; [eapply hoare_if_wp|]]
      end.

Ltac hauto :=
  intros;
  match goal with
  | [|- {{_}} _ {{_}}] => repeat hauto_split1
  | _ => idtac
  end;
  try (intros; apply assert_implies_refl);
  try (hauto_vc; fail);
  try (exact (t_empty 0)).

Ltac hauto_while P :=
  intros;
  first[
      eapply (hoare_while P) |
      eapply hoare_consequence_post; [eapply (hoare_while P)|] |
      eapply hoare_consequence_post; [eapply hoare_consequence_pre; [eapply (hoare_while P)|]|]
    ];
  hauto.

Arguments div x y : simpl never.

(** ############################################################### **)
(**                                                                 **)
(** *             STLC: Simply Typed Lambda Calculus                **)
(**                                                                 **)
(** ############################################################### **)

(* ################################################################# *)
(** * Syntax *)

Inductive ty : Type :=
  | Ty_Arrow : ty -> ty -> ty
  | Ty_Nat  : ty
  | Ty_Sum  : ty -> ty -> ty
  | Ty_List : ty -> ty
  | Ty_Unit : ty
  | Ty_Prod : ty -> ty -> ty
.

Inductive tm : Type :=
  (* pure STLC for Ty_Arrow *)
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> ty -> tm -> tm
  (* numbers for Ty_Nat *)
  | tm_const: nat -> tm
  | tm_plus : tm -> tm -> tm
  | tm_minus : tm -> tm -> tm
  | tm_mult : tm -> tm -> tm
  | tm_if0  : tm -> tm -> tm -> tm
  (* sums for Ty_Sum *)
  | tm_inl : ty -> tm -> tm     (* tm_inl Unit (tm_const 3) : Ty_Sum Ty_Nat Unit *)
  | tm_inr : ty -> tm -> tm     (* tm_inr Unit (tm_const 3) : Ty_Sum Unit Ty_Nat *)
  | tm_case : tm -> string -> tm -> string -> tm -> tm
          (* i.e., [match t0 with | inl x1 => t1 | inr x2 => t2 end] *)
  (* lists for Ty_List *)
  | tm_nil : ty -> tm
  | tm_cons : tm -> tm -> tm
  | tm_lcase : tm -> tm -> string -> string -> tm -> tm
           (* i.e., [match t1 with | nil => t2 | x::y => t3 end] *)
  (* unit for Ty_Unit *)
  | tm_unit : tm

  (* pairs for Ty_Prod *)
  | tm_pair : tm -> tm -> tm
  | tm_fst : tm -> tm
  | tm_snd : tm -> tm

  (* let for Ty_Arrow *)
  | tm_let : string -> tm -> tm -> tm
                     
  (* fix for Ty_Arrow *)
  | tm_fix  : tm -> tm
.

Declare Scope stlc_scope.
Delimit Scope stlc_scope with stlc.
Open Scope stlc_scope.

Declare Custom Entry stlc_ty.
Declare Custom Entry stlc_tm.

Notation "x" := x (in custom stlc_ty at level 0, x global) : stlc_scope.

(* Notation "<{{ x }}>" := x (x custom stlc_ty). *)

Notation "( t )" := t (in custom stlc_ty at level 0, t custom stlc_ty) : stlc_scope.
Notation "S -> T" := (Ty_Arrow S T) (in custom stlc_ty at level 99, right associativity) : stlc_scope.

Notation "$( t )" := t (in custom stlc_ty at level 0, t constr) : stlc_scope.

Notation "$( x )" := x (in custom stlc_tm at level 0, x constr, only parsing) : stlc_scope.
Notation "x" := x (in custom stlc_tm at level 0, x constr at level 0) : stlc_scope.
Notation "<{{ e }}>" := e (e custom stlc_tm at level 200) : stlc_scope.
Notation "( x )" := x (in custom stlc_tm at level 0, x custom stlc_tm) : stlc_scope.

Notation "x y" := (tm_app x y) (in custom stlc_tm at level 10, left associativity) : stlc_scope.
Notation "\ x : t , y" :=
  (tm_abs x t y) (in custom stlc_tm at level 200, x global,
                     t custom stlc_ty,
                     y custom stlc_tm at level 200,
                     left associativity).
Coercion tm_var : string >-> tm.
Arguments tm_var _%_string.

Notation "'Nat'" := Ty_Nat (in custom stlc_ty at level 0).
Notation "x + y" := (tm_plus x y) (in custom stlc_tm at level 95,
                                      right associativity) : stlc_scope.
Notation "x - y" := (tm_minus x y) (in custom stlc_tm at level 95,
                                      right associativity) : stlc_scope.
Notation "x * y" := (tm_mult x y) (in custom stlc_tm at level 95,
                                      right associativity) : stlc_scope.
Notation "'if0' x 'then' y 'else' z" :=
  (tm_if0 x y z) (in custom stlc_tm at level 0,
                    x custom stlc_tm at level 0,
                    y custom stlc_tm at level 0,
                    z custom stlc_tm at level 0) : stlc_scope.

Coercion tm_const : nat >-> tm.

Notation "S + T" :=
  (Ty_Sum S T) (in custom stlc_ty at level 3, left associativity) : stlc_scope.
Notation "'inl' T t" := (tm_inl T t) (in custom stlc_tm at level 10,
                                         T custom stlc_ty,
                                         t custom stlc_tm at level 0) : stlc_scope.
Notation "'inr' T t" := (tm_inr T t) (in custom stlc_tm at level 10,
                                         T custom stlc_ty,
                                         t custom stlc_tm at level 0) : stlc_scope.
Notation "'case' t0 'of' '|' 'inl' x1 '=>' t1 '|' 'inr' x2 '=>' t2" :=
  (tm_case t0 x1 t1 x2 t2) (in custom stlc_tm at level 200,
                               t0 custom stlc_tm at level 200,
                               x1 global,
                               t1 custom stlc_tm at level 200,
                               x2 global,
                               t2 custom stlc_tm at level 200,
                               left associativity): stlc_scope.

Notation "X * Y" :=
  (Ty_Prod X Y) (in custom stlc_ty at level 2, X custom stlc_ty, Y custom stlc_ty at level 0) : stlc_scope.

Notation "( x ',' y )" := (tm_pair x y) (in custom stlc_tm at level 0,
                                                x custom stlc_tm,
                                                y custom stlc_tm) : stlc_scope.
Notation "t '.fst'" := (tm_fst t) (in custom stlc_tm at level 1) : stlc_scope.
Notation "t '.snd'" := (tm_snd t) (in custom stlc_tm at level 1) : stlc_scope.

Notation "'List' T" :=
  (Ty_List T) (in custom stlc_ty at level 4) : stlc_scope.
Notation "'List' T" := (Ty_List T) (at level 0) : stlc_scope.
Notation "'nil' T" := (tm_nil T) (in custom stlc_tm at level 0, T custom stlc_ty) : stlc_scope.
Notation "h '::' t" := (tm_cons h t) (in custom stlc_tm at level 2, right associativity) : stlc_scope.
Notation "'case' t1 'of' '|' 'nil' '=>' t2 '|' x '::' y '=>' t3" :=
  (tm_lcase t1 t2 x y t3) (in custom stlc_tm at level 200,
                              t1 custom stlc_tm at level 200,
                              t2 custom stlc_tm at level 0,
                              x global,
                              y global,
                              t3 custom stlc_tm at level 0,
                              left associativity) : stlc_scope.

Notation "'Unit'" :=
  (Ty_Unit) (in custom stlc_ty at level 0) : stlc_scope.
Notation "'unit'" := tm_unit (in custom stlc_tm at level 0) : stlc_scope.

Notation "'let' x '=' t1 'in' t2" :=
  (tm_let x t1 t2) (in custom stlc_tm at level 200) : stlc_scope.

Notation "'fix' t" := (tm_fix t) (in custom stlc_tm at level 200) : stlc_scope.

(* ################################################################# *)
(** * Evaluation Relation *)

(* ----------------------------------------------------------------- *)
(** *** Substitution *)

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc_tm at level 5, x global, s custom stlc_tm,
      t custom stlc_tm at next level, right associativity).

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  (* pure STLC *)
  | tm_var y =>
      if String.eqb x y then s else t
  | <{{\y:T, t1}}> =>
      if String.eqb x y then t else <{{\y:T, [x:=s] t1}}>
  | <{{t1 t2}}> =>
      <{{([x:=s] t1) ([x:=s] t2)}}>
  (* numbers *)
  | tm_const _ =>
      t
  | <{{t1 + t2}}> =>
      <{{ ([x := s] t1) + ([x := s] t2)}}>
  | <{{t1 - t2}}> =>
      <{{ ([x := s] t1) - ([x := s] t2)}}>
  | <{{t1 * t2}}> =>
      <{{ ([x := s] t1) * ([x := s] t2)}}>
  | <{{if0 t1 then t2 else t3}}> =>
      <{{if0 ([x := s] t1) then ([x := s] t2) else ([x := s] t3)}}>
  (* sums *)
  | <{{inl T2 t1}}> =>
      <{{inl T2 ( [x:=s] t1) }}>
  | <{{inr T1 t2}}> =>
      <{{inr T1 ( [x:=s] t2) }}>
  | <{{case t0 of | inl y1 => t1 | inr y2 => t2}}> =>
      <{{case ([x:=s] t0) of
         | inl y1 => $(if String.eqb x y1 then t1 else <{{ [x:=s] t1 }}> )
         | inr y2 => $(if String.eqb x y2 then t2 else <{{ [x:=s] t2 }}> ) }}>
  (* lists *)
  | <{{nil T}}> =>
      t
  | <{{t1 :: t2}}> =>
      <{{ ([x:=s] t1) :: ([x:=s] t2) }}>
  | <{{case t1 of | nil => t2 | y1 :: y2 => t3}}> =>
      <{{case ( [x:=s] t1 ) of
        | nil => ([x:=s] t2)
        | y1 :: y2 =>
        $(if String.eqb x y1 then t3
          else if String.eqb x y2 then t3
               else <{{ [x:=s] t3 }}>) }}>
  (* unit *)
  | <{{unit}}> => <{{unit}}>

  (* pairs *)
  | <{{(t1,t2)}}> => <{{ ([x:=s] t1, [x:=s]t2) }}>
  | <{{t.fst}}> => <{{([x:=s]t).fst}}>
  | <{{t.snd}}> => <{{([x:=s]t).snd}}>

  (* let *)
  | <{{let y = t1 in t2}}> =>
    <{{let y = ([x:=s] t1) in $(if String.eqb x y then t2 else <{{[x:=s] t2}}>) }}>

  (* fix *)
  | <{{fix t}}> => <{{fix ([x:=s] t)}}>
  end

where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc_tm) : stlc_scope.

(** *** Value *)

Inductive value : tm -> Prop :=
  (* In pure STLC, function abstractions are values: *)
  | v_abs : forall x T2 t1,
      value <{{\x:T2, t1}}>
  (* Numbers are values: *)
  | v_nat : forall n : nat,
      value <{{n}}>
  (* A tagged value is a value:  *)
  | v_inl : forall v T1,
      value v ->
      value <{{inl T1 v}}>
  | v_inr : forall v T1,
      value v ->
      value <{{inr T1 v}}>
  (* A list is a value iff its head and tail are values: *)
  | v_lnil : forall T1, value <{{nil T1}}>
  | v_lcons : forall v1 v2,
      value v1 ->
      value v2 ->
      value <{{v1 :: v2}}>
  (* A unit is always a value *)
  | v_unit : value <{{unit}}>
  (* A pair is a value if both components are: *)
  | v_pair : forall v1 v2,
      value v1 ->
      value v2 ->
      value <{{(v1, v2)}}>.

Hint Constructors value : core.

(** *** Step *)

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  (* pure STLC *)
  | ST_AppAbs : forall x T2 t1 v2,
         value v2 ->
         <{{(\x:T2, t1) v2}}> --> <{{ [x:=v2]t1 }}>
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{{t1 t2}}> --> <{{t1' t2}}>
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{{v1 t2}}> --> <{{v1  t2'}}>
  (* numbers *)
      
  | ST_Plusconsts : forall n1 n2 : nat,
         <{{n1 + n2}}> --> <{{ $(n1 + n2) }}>
  | ST_Plus1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{{t1 + t2}}> --> <{{t1' + t2}}>
  | ST_Plus2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{{v1 + t2}}> --> <{{v1 + t2'}}>
  | ST_Minusconsts : forall n1 n2 : nat,
         <{{n1 - n2}}> --> <{{ $(n1 - n2) }}>
  | ST_Minus1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{{t1 - t2}}> --> <{{t1' - t2}}>
  | ST_Minus2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{{v1 - t2}}> --> <{{v1 - t2'}}>
  | ST_Mulconsts : forall n1 n2 : nat,
         <{{n1 * n2}}> --> <{{ $(n1 * n2) }}>
  | ST_Mult1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{{t1 * t2}}> --> <{{t1' * t2}}>
  | ST_Mult2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{{v1 * t2}}> --> <{{v1 * t2'}}>
  | ST_If0 : forall t1 t1' t2 t3,
         t1 --> t1' ->
         <{{if0 t1 then t2 else t3}}> --> <{{if0 t1' then t2 else t3}}>
  | ST_If0_Zero : forall t2 t3,
         <{{if0 0 then t2 else t3}}> --> t2
  | ST_If0_Nonzero : forall n t2 t3,
         <{{if0 $(S n) then t2 else t3}}> --> t3
  (* sums *)
  | ST_Inl : forall t1 t1' T2,
        t1 --> t1' ->
        <{{inl T2 t1}}> --> <{{inl T2 t1'}}>
  | ST_Inr : forall t2 t2' T1,
        t2 --> t2' ->
        <{{inr T1 t2}}> --> <{{inr T1 t2'}}>
  | ST_Case : forall t0 t0' x1 t1 x2 t2,
        t0 --> t0' ->
        <{{case t0 of | inl x1 => t1 | inr x2 => t2}}> -->
        <{{case t0' of | inl x1 => t1 | inr x2 => t2}}>
  | ST_CaseInl : forall v0 x1 t1 x2 t2 T2,
        value v0 ->
        <{{case inl T2 v0 of | inl x1 => t1 | inr x2 => t2}}> --> <{{ [x1:=v0]t1 }}>
  | ST_CaseInr : forall v0 x1 t1 x2 t2 T1,
        value v0 ->
        <{{case inr T1 v0 of | inl x1 => t1 | inr x2 => t2}}> --> <{{ [x2:=v0]t2 }}>
  (* lists *)
  | ST_Cons1 : forall t1 t1' t2,
       t1 --> t1' ->
       <{{t1 :: t2}}> --> <{{t1' :: t2}}>
  | ST_Cons2 : forall v1 t2 t2',
       value v1 ->
       t2 --> t2' ->
       <{{v1 :: t2}}> --> <{{v1 :: t2'}}>
  | ST_Lcase1 : forall t1 t1' t2 x1 x2 t3,
       t1 --> t1' ->
       <{{case t1 of | nil => t2 | x1 :: x2 => t3}}> -->
       <{{case t1' of | nil => t2 | x1 :: x2 => t3}}>
  | ST_LcaseNil : forall T1 t2 x1 x2 t3,
       <{{case nil T1 of | nil => t2 | x1 :: x2 => t3}}> --> t2
  | ST_LcaseCons : forall v1 vl t2 x1 x2 t3,
       value v1 ->
       value vl ->
       <{{case v1 :: vl of | nil => t2 | x1 :: x2 => t3}}>
         -->  <{{ [x2 := vl] ([x1 := v1] t3) }}>
  (* pairs *)
  | ST_Pair1 : forall t1 t1' t2,
       t1 --> t1' ->
       <{{(t1, t2)}}> --> <{{(t1',  t2)}}>
  | ST_Pair2 : forall v1 t2 t2',
       value v1 ->
       t2 --> t2' ->
       <{{(v1, t2)}}> --> <{{(v1, t2')}}>
  | ST_Fst : forall t1 t1',
       t1 --> t1' ->
       <{{t1.fst}}> --> <{{t1'.fst}}>
  | ST_FstPair : forall v1 v2,
       value v1 ->
       value v2 ->
       <{{(v1,v2).fst}}> --> <{{ v1 }}>
  | ST_Snd : forall t1 t1',
       t1 --> t1' ->
       <{{t1.snd}}> --> <{{t1'.snd}}>
  | ST_SndPair : forall v1 v2,
       value v1 ->
       value v2 ->
       <{{(v1,v2).snd}}> --> <{{ v2 }}>
  (* let *)
  | ST_Let : forall x t1 t1' t2,
       t1 --> t1' ->
       <{{let x = t1 in t2}}> --> <{{let x = t1' in t2}}>
  | ST_LetVal : forall x v1 t2,
       value v1 ->
       <{{let x = v1 in t2}}> --> <{{ [x:=v1]t2 }}>
  (* fix *)
  | ST_Fix : forall t1 t1',
       t1 --> t1' ->
       <{{fix t1}}> --> <{{fix t1'}}>
  | ST_FixAbs : forall f T t,
       <{{fix (\f:T, t)}}> --> <{{ [f := fix (\f:T, t) ] t }}>

  where "t '-->' t'" := (step t t').

Hint Constructors step : core.

(* ################################################################# *)
(** * Typing Relation *)

Definition context := partial_map ty.

Reserved Notation "Gamma '|--' t '\in' T"
            (at level 40, t custom stlc_tm, T custom stlc_ty at level 0).

Inductive has_type : context -> tm -> ty -> Prop :=
  (* pure STLC *)
  | T_Var : forall Gamma x T1,
      Gamma x = Some T1 ->
      Gamma |-- x \in T1
  | T_Abs : forall Gamma x T1 T2 t1,
      (x |-> T2 ; Gamma) |-- t1 \in T1 ->
      Gamma |-- \x:T2, t1 \in (T2 -> T1)
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |-- t1 \in (T2 -> T1) ->
      Gamma |-- t2 \in T2 ->
      Gamma |-- t1 t2 \in T1
  (* numbers *)
  | T_Nat : forall Gamma (n : nat),
      Gamma |-- n \in Nat
  | T_Plus : forall Gamma t1 t2,
      Gamma |-- t1 \in Nat ->
      Gamma |-- t2 \in Nat ->
      Gamma |-- t1 + t2 \in Nat
  | T_Minus : forall Gamma t1 t2,
      Gamma |-- t1 \in Nat ->
      Gamma |-- t2 \in Nat ->
      Gamma |-- t1 - t2 \in Nat
  | T_Mult : forall Gamma t1 t2,
      Gamma |-- t1 \in Nat ->
      Gamma |-- t2 \in Nat ->
      Gamma |-- t1 * t2 \in Nat
  | T_If0 : forall Gamma t1 t2 t3 T0,
      Gamma |-- t1 \in Nat ->
      Gamma |-- t2 \in T0 ->
      Gamma |-- t3 \in T0 ->
      Gamma |-- if0 t1 then t2 else t3 \in T0
  (* sums *)
  | T_Inl : forall Gamma t1 T1 T2,
      Gamma |-- t1 \in T1 ->
      Gamma |-- (inl T2 t1) \in (T1 + T2)
  | T_Inr : forall Gamma t2 T1 T2,
      Gamma |-- t2 \in T2 ->
      Gamma |-- (inr T1 t2) \in (T1 + T2)
  | T_Case : forall Gamma t0 x1 T1 t1 x2 T2 t2 T3,
      Gamma |-- t0 \in (T1 + T2) ->
      (x1 |-> T1 ; Gamma) |-- t1 \in T3 ->
      (x2 |-> T2 ; Gamma) |-- t2 \in T3 ->
      Gamma |-- (case t0 of | inl x1 => t1 | inr x2 => t2) \in T3
  (* lists *)
  | T_Nil : forall Gamma T1,
      Gamma |-- (nil T1) \in (List T1)
  | T_Cons : forall Gamma t1 t2 T1,
      Gamma |-- t1 \in T1 ->
      Gamma |-- t2 \in (List T1) ->
      Gamma |-- (t1 :: t2) \in (List T1)
  | T_Lcase : forall Gamma t1 T1 t2 x1 x2 t3 T2,
      Gamma |-- t1 \in (List T1) ->
      Gamma |-- t2 \in T2 ->
      (x1 |-> T1 ; x2 |-> <{{List T1}}> ; Gamma) |-- t3 \in T2 ->
      Gamma |-- (case t1 of | nil => t2 | x1 :: x2 => t3) \in T2
  (* unit *)
  | T_Unit : forall Gamma,
      Gamma |-- unit \in Unit

  (* pairs *)
  | T_Pair : forall Gamma t1 t2 T1 T2,
      Gamma |-- t1 \in T1 ->
      Gamma |-- t2 \in T2 ->
      Gamma |-- (t1,  t2) \in (T1 * T2)
  | T_Fst : forall Gamma t T1 T2,
      Gamma |-- t \in (T1 * T2) ->
      Gamma |-- t.fst \in T1
  | T_Snd : forall Gamma t T1 T2,
      Gamma |-- t \in (T1 * T2) ->
      Gamma |-- t.snd \in T2
  (* let *)
  | T_Let : forall Gamma x t1 t2 T1 T2,
      Gamma |-- t1 \in T1 ->
      (x |-> T1; Gamma) |-- t2 \in T2 ->
      Gamma |-- let x = t1 in t2 \in T2
  (* fix *)
  | T_Fix : forall Gamma t T,
      Gamma |-- t \in (T -> T) ->
      Gamma |-- fix t \in T

where "Gamma '|--' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type : core.

(* ################################################################# *)
(** * Definitions and Tactics for muti-step evaluation *)

Inductive multi {X:Type} (R: relation X) : relation X :=
  | multi_refl  : forall (x y: X) (EQ: x = y), multi R x y
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Notation " t '==>*' t' " := (multi step t t') (at level 40).

Hint Constructors multi : core.

Theorem multi_trans :
  forall (X:Type) (R: relation X) (x y z : X),
      multi R x y  ->
      multi R y z ->
      multi R x z.
Proof.
  intros. induction H; subst; eauto.
Qed.

Definition normal_form {X:Type} (R:relation X) (t:X) : Prop :=
  ~ exists t', R t t'.

Definition step_normal_form := normal_form step.

Definition normal_form_of (t t' : tm) :=
  (t ==>* t' /\ step_normal_form t').

Definition stuck (t:tm) : Prop :=
  normal_form step t /\ ~ value t.

(** *** Tactics [normalize] *)

Tactic Notation "normalize1" :=
  eapply multi_step ; [ (eauto 20 using step; fail) | simpl].

Tactic Notation "normalize" :=
   repeat normalize1;
   try (apply multi_refl; repeat apply f_equal; eauto; nia).

(* Fix a minor bug about eauto. *)
Lemma trivial_refl: forall T (x: T), x = x.
  eauto.
Qed.
Hint Resolve trivial_refl: core.

(** ############################################################### **)
(**                                                                 **)
(** *           Definitions and Tactics for Final Exam              **)
(**                                                                 **)
(** ############################################################### **)

Definition FILL_IN_HERE {T: Type} : T.  Admitted.

(** Important: 

    - Just leave [exact FILL_IN_HERE] for those problems that you fail to prove.
**)

(**
    - Here is the list of tactics and tacticals you have learned.

      [intros]
      [revert]
      [reflexivity]
      [simpl]
      [rewrite]
      [induction]
      [assert]
      [unfold]
      [apply] ... [with] ... [in] ...
      [destruct] ... [as] ... [eqn:] ...
      [inversion]
      [symmetry]
      [generalize dependent]
      [split]
      [exists]
      [clear]
      [subst]
      [rename] ... [into] ...
      [contradiction]
      [constructor]
      [auto]
      [repeat]
      [try]
      [remember] ... [as] ...
      [replace] ... [with] ...
      [eauto]
      [nia]
      [;]
**)

(** IMPORTANT!!

   You can use the very powerful tactic [nia].
   [nia] can solve arithmetic problems automatically.
*)

(* ################################################################# *)
(** * Names for Variables *)

Definition F : string := "F".
Definition G : string := "G".
Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".
Definition I : string := "I".
Definition J : string := "J".
Definition P : string := "P".
Definition T : string := "T".
Definition N : string := "N".
Definition SELF: string := "SELF".
Definition RES : string := "RES".

(* ################################################################# *)
(** * Program Definitions *)

(** summation *)

Fixpoint sum_to_n (n: nat) : nat :=
  match n with
  | 0 => 0
  | S n' => n + sum_to_n n'
  end.

(** *** to_tmlist *)

Fixpoint to_tmlist (l: list nat) : tm :=
  match l with
  | nil => <{{ nil Nat }}>
  | n :: l' => let tm := to_tmlist l' in
               <{{ n :: tm }}>
  end.

Fixpoint sum_list (l: list nat) : nat :=
  match l with
  | [] => 0
  | hd :: tl => hd + sum_list tl
  end.

(** *** Optimize Assignment *)

Fixpoint aexp_subst (x: string) (xa: aexp) (a: aexp) : aexp :=
  match a with
  | ANum _ => a
  | AId y => if (x =? y)%string then xa else a
  | APlus a1 a2 => APlus (aexp_subst x xa a1) (aexp_subst x xa a2) 
  | AMinus a1 a2 => AMinus (aexp_subst x xa a1) (aexp_subst x xa a2) 
  | AMult a1 a2 => AMult (aexp_subst x xa a1) (aexp_subst x xa a2)
  | AGet a1 a2 => AGet (aexp_subst x xa a1) (aexp_subst x xa a2)
  | ASet a1 a2 a3 => ASet (aexp_subst x xa a1) (aexp_subst x xa a2) (aexp_subst x xa a3)
  end.

Definition aexp_div_subst (x: string) (xa: aexp) (a: aexp_div) : aexp_div :=
  match a with
  | AExp a => AExp (aexp_subst x xa a)
  | ADiv a1 a2 => ADiv (aexp_subst x xa a1) (aexp_subst x xa a2)
  end.

Fixpoint optimize_if_while (c: com) : com :=
  match c with
  | <{ skip }> | <{ _ := _ }> => c
  | <{ c1 ; c2 }>  =>
      <{ optimize_if_while c1; optimize_if_while c2 }>
  | <{ if b then c1 else c2 end }> =>
      match b with
      | BTrue => c1
      | BFalse => c2
      | _ => c
      end
  | <{ while b do c0 end }> =>
      match b with
      | BFalse => <{ skip }>
      | BTrue => <{ c0; c }>
      | _ => c
      end
  end.

(** *** Bubble Sort *)

Definition SIZE : string := "SIZE".
Definition ARRAY : string := "ARRAY".

Definition SZ : string := "SZ".
Definition CUR : string := "CUR".
Definition NEXT : string := "NEXT".

Definition bubble_sort_com : com :=
  <{
  SZ := SIZE;
  while (SZ >= 1) do
    I := 0;
    while (I < SZ - 1) do
      CUR := ARRAY @ I;
      NEXT := ARRAY @ (I + 1);
      if CUR > NEXT then
        ARRAY := ARRAY <| I ~> NEXT |> <| I + 1 ~> CUR |>
      else
        skip
      end;
      I := I + 1
    end;
    SZ := SZ -1
  end
  }>.

Definition SortedRange (l: list nat) (min max: nat) : Prop :=
  forall i (MIN: min <= i) (MAX: i < max - 1) (RANGE: max <= Lists.List.length l),
    nth i l 0 <= nth (S i) l 0.

Definition Sorted (l: list nat) : Prop := SortedRange l 0 (Lists.List.length l).

Definition Bounded (l: list nat) (idx: nat) : Prop :=
  forall i (LT: i < idx) (RANGE: idx < Lists.List.length l),
    nth i l 0 <= nth idx l 0.

