Set Warnings "-notation-overridden,-notation-incompatible-prefix".
From Stdlib Require Import Bool.
From Stdlib Require Import Init.Nat.
From Stdlib Require Import Arith.
From Stdlib Require Import EqNat. Import Nat.
From Stdlib Require Import Lia.
From Stdlib Require Import List. Import ListNotations.
From Stdlib Require Import Strings.String.
From PLF Require Import Maps.
Set Default Goal Selector "!".

Require Import Program Program.Wf.


(**** Useful tactics ****)

Lemma __mp__: forall P Q: Type, P -> (P -> Q) -> Q.
Proof. intuition. Defined.

Ltac hexploit H := eapply __mp__; [eapply H|].

Ltac on_last_hyp tac :=
  match goal with [ H : _ |- _ ] => first [ tac H | fail 1 ] end.

Ltac revert_until id :=
  on_last_hyp ltac:(fun id' =>
    match id' with
      | id => idtac
      | _ => revert id' ; revert_until id
    end).


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
