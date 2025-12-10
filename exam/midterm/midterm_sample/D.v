(** Mid Exam *)

Definition FILL_IN_HERE {T: Type} : T.  Admitted.

(** Important: 

    - Just leave [exact FILL_IN_HERE] for those problems that you fail to prove.

    - You are NOT allowed to use the following tactics.

      [tauto], [intuition], [firstorder].
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

   You can use a very powerful tactic, [nia].
   [nia] can solve arithmetic problems automatically.
*)

Require Export String Lia Nat PeanoNat.

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

(**
  Definition of [list] 
 **)

Require Export List.

(* Imported from the library *)

(***
Inductive list (X:Type) : Type :=
| nil : list X
| cons : X -> list X -> list X.

Arguments nil {X}.
Arguments cons {X} _ _.

Fixpoint app (X : Type) (l1 l2 : list X)
  : (list X) :=
  match l1 with
  | nil      => l2
  | cons h t => cons h (app X t l2)
  end.

Arguments app {X} l1 l2.

Notation "x :: y" := (cons x y)
                       (at level 60, right associativity).
Notation "x ++ y" := (app x y)
                       (at level 60, right associativity).

***)

Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).

Check (3 :: ([0; 1] ++ [])).

(**
  Definition of [bubble_sort] 
 **)

Fixpoint insert {X} (lex: X -> X -> bool) (x: X) (l: list X): list X :=
  match l with
  | [] => [x]
  | hd :: tl => if lex x hd then x :: hd :: tl else hd :: insert lex x tl
  end.

Fixpoint bubble_sort {X} (lex: X -> X -> bool) (l: list X): list X :=
  match l with
  | [] => []
  | hd :: tl => insert lex hd (bubble_sort lex tl)
  end.

Compute bubble_sort leb [3;0;1;8;5].

