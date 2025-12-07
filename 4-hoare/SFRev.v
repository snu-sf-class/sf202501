Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
Set Warnings "-intuition-auto-with-star".
From Stdlib Require Import Strings.String.
From PLF Require Import Maps.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import EqNat.
From Stdlib Require Import PeanoNat. Import Nat.
From Stdlib Require Import Lia.
From PLF Require Export SFImp.
From PLF Require Import SFHoare.
From PLF Require Import SFHoare2.
Set Default Goal Selector "!".

Require Import List.
Import ListNotations.

Require Import Permutation.

(***
  Array Reversal
 ***)


(* Program Code *)

Definition SIZE : string := "SIZE".
Definition IN : string := "IN".
Definition OUT : string := "OUT".

Definition I : string := "I".

Definition ex_rev : com :=
  <{
      I := 0;
      while (I < SIZE) do
          OUT := OUT <| I ~> IN @ (SIZE - 1 - I) |>;
          I := I + 1
      end
  }>.

(* Prove the correctness of [ex_rev] *)

Theorem rev_correct (array: list nat) :
  let size := length array
  in
  {{$(fun st => st SIZE = size /\ arr2list (st IN) size = array )}}
    ex_rev
  {{$(fun st => arr2list (st OUT) size = rev array )}}.
Proof.
Admitted.






(****
   Solution
 ****)

Fixpoint prefix (k: nat) (l: list nat) : list nat :=
  match k with
  | 0 => []
  | S k' => match l with
            | [] => []
            | hd :: tl => hd :: prefix k' tl
            end
  end.

Lemma prefix_succ k l
  (RANGE: k < length l)
  :
  prefix (k + 1) l = prefix k l ++ [nth k l 0].
Proof.
  revert_until k. induction k; destruct l; simpl; eauto; try nia.
  intros. rewrite IHk; eauto. nia.
Qed.

Lemma prefix_full l:
  prefix (length l) l = l.
Proof.
  induction l; eauto.
  simpl. rewrite IHl. eauto.
Qed.

Theorem rev_correct_sol (array: list nat) :
  let size := length array
  in
  {{$(fun st => st SIZE = size /\ arr2list (st IN) size = array )}}
    ex_rev
  {{$(fun st => arr2list (st OUT) size = rev array )}}.
Proof.
  unfold ex_rev. hauto.
  { hauto_while (fun st =>
                 let size := length array in
                 st SIZE = size /\ arr2list (st IN) size = array /\ st I <= size /\
                 prefix (size - st I) array ++ rev (arr2list (st OUT) (st I)) = array).
    { hauto_vc.
      rewrite <-H3 at 3.
      replace (length array - st I) with (length array - (st I + 1) + 1) by nia.
      rewrite prefix_succ; try nia. rewrite <-app_assoc. f_equal.
      rewrite arr2list_set; try nia.
      rewrite arr2list_plus_one.
      eassert (EQ := set_nth_spec _ _ _ [] _). rewrite !app_nil_r in EQ.
      rewrite EQ; [|rewrite arr2list_length; nia].
      rewrite rev_app_distr. simpl.
      erewrite arr2list_get, H1; try nia.
      do 2 f_equal. nia.
    }
    { hauto_vc.
      rewrite <-H3 at 2.
      replace (length array - st I) with 0 by nia. simpl.
      rewrite rev_involutive. replace (st I) with (length array) by nia. eauto.
    }
  }
  { hauto_vc.
    rewrite app_nil_r.
    rewrite <-(prefix_full array) at 3.
    f_equal. nia.
  }
Qed.
