(** * Imp: Simple Imperative Programs *)

(** In this chapter, we take a more serious look at how to use Coq as
    a tool to study other things.  Our case study is a _simple
    imperative programming language_ called Imp, embodying a tiny core
    fragment of conventional mainstream languages such as C and Java.

    Here is a familiar mathematical function written in Imp.

       Z := X;
       Y := 1;
       while Z <> 0 do
         Y := Y * Z;
         Z := Z - 1
       end
*)

(** We concentrate here on defining the _syntax_ and _semantics_ of
    Imp; later, in _Programming Language Foundations_ (_Software
    Foundations_, volume 2), we develop a theory of _program
    equivalence_ and introduce _Hoare Logic_, a popular logic for
    reasoning about imperative programs. *)

Set Warnings "-notation-overridden,-notation-incompatible-prefix".
From Stdlib Require Import Bool.
From Stdlib Require Import Init.Nat.
From Stdlib Require Import Arith.
From Stdlib Require Import EqNat. Import Nat.
From Stdlib Require Import Lia.
From Stdlib Require Import List. Import ListNotations.
From Stdlib Require Import Strings.String.
From PLF Require Import Maps.
From PLF Require Export SFArray.
Set Default Goal Selector "!".

Definition state := total_map nat.

(* ================================================================= *)
(** ** Syntax  *)

(** We can add variables to the arithmetic expressions we had before
    simply by including one more constructor: *)

Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string)              (* <--- NEW *)
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

(** Defining a few variable names as notational shorthands will make
    examples easier to read: *)

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

(** (This convention for naming program variables ([X], [Y],
    [Z]) clashes a bit with our earlier use of uppercase letters for
    types.  Since we're not using polymorphism heavily in the chapters
    developed to Imp, this overloading should not cause confusion.) *)

(** The definition of [bexp]s is unchanged (except that it now refers
    to the new [aexp]s): *)

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

(** To make Imp programs easier to read and write, we introduce some
    notations and implicit coercions.  *)

(** You do not need to understand exactly what these declarations do.

    Briefly, though:
       - The [Coercion] declaration stipulates that a function (or
         constructor) can be implicitly used by the type system to
         coerce a value of the input type to a value of the output
         type.  For instance, the coercion declaration for [AId]
         allows us to use plain strings when an [aexp] is expected;
         the string will implicitly be wrapped with [AId].
       - [Declare Custom Entry com] tells Coq to create a new "custom
         grammar" for parsing Imp expressions and programs. The first
         notation declaration after this tells Coq that anything
         between [<{] and [}>] should be parsed using the Imp
         grammar. Again, it is not necessary to understand the
         details, but it is important to recognize that we are
         defining _new_ interpretations for some familiar operators
         like [+], [-], [*], [=], [<=], etc., when they occur between
         [<{] and [}>]. *)

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

(** We can now write [3 + (X * 2)] instead  of [APlus 3 (AMult X 2)],
    and [true && ~(X <= 4)] instead of [BAnd true (BNot (BLe X 4))]. *)

Definition example_aexp : aexp := <{ 3 + (X * 2) }>.
Definition example_bexp : bexp := <{ true && ~(X <= 4) }>.
Definition example_aexp2 : aexp := <{ X @ (Y + 3) }>.
Definition example_aexp3 : aexp := <{ X <| Y ~> Z |> }>.

(* ================================================================= *)
(** ** Evaluation *)

(** The arith and boolean evaluators must now be extended to
    handle variables in the obvious way, taking a state [st] as an
    extra argument: *)

Fixpoint aeval (st : state) (* <--- NEW *)
               (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x                                (* <--- NEW *)
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

Fixpoint beval (st : state) (* <--- NEW *)
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

(** We can use our notation for total maps in the specific case of
    states -- i.e., we write the empty state as [(_ !-> 0)]. *)

Definition empty_st := (_ !-> 0).

(** Also, we can add a notation for a "singleton state" with just one
    variable bound to a value. *)
Notation "x '!->' v" := (x !-> v ; empty_st) (at level 100, v at level 200).

Example aexp1 :
    aeval (X !-> 5) <{ 3 + (X * 2) }>
  = 13.
Proof. reflexivity. Qed.
Example aexp2 :
    aeval (X !-> 5 ; Y !-> 4) <{ Z + (X * Y) }>
  = 20.
Proof. reflexivity. Qed.

Example bexp1 :
    beval (X !-> 5) <{ true && ~(X <= 4) }>
  = true.
Proof. reflexivity. Qed.

(* ################################################################# *)
(** * Commands *)

(** Now we are ready to define the syntax and behavior of Imp
    _commands_ (or _statements_). *)

(* ================================================================= *)
(** ** Syntax *)

(** Informally, commands [c] are described by the following BNF
    grammar.

     c := skip
        | x := a
        | c ; c
        | if b then c else c end
        | while b do c end
*)

(** Here is the formal definition of the abstract syntax of
    commands: *)

Inductive com : Type :=
  | CSkip
  | CAsgn (x : string) (a : aexp_div)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

(** As we did for expressions, we can use a few [Notation]
    declarations to make reading and writing Imp programs more
    convenient. *)

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

(** For example, here is the factorial function again, written as a
    formal Coq definition.  When this command terminates, the variable
    [Y] will contain the factorial of the initial value of [X]. *)

Definition fact_in_coq : com :=
  <{ Z := X;
     Y := 1;
     while Z <> 0 do
       Y := Y * Z;
       Z := Z - 1
     end }>.

Print fact_in_coq.

(* ================================================================= *)
(** ** Desugaring Notations *)

(** Coq offers a rich set of features to manage the increasing
    complexity of the objects we work with, such as coercions and
    notations. However, their heavy usage can make it hard to
    understand what the expressions we enter actually mean. In such
    situations it is often instructive to "turn off" those features to
    get a more elementary picture of things, using the following
    commands:

    - [Unset Printing Notations] (undo with [Set Printing Notations])
    - [Set Printing Coercions] (undo with [Unset Printing Coercions])
    - [Set Printing All] (undo with [Unset Printing All])

    These commands can also be used in the middle of a proof, to
    elaborate the current goal and context. *)

Unset Printing Notations.
Print fact_in_coq.
(* ===>
   fact_in_coq =
   CSeq (CAsgn Z X)
        (CSeq (CAsgn Y (S O))
              (CWhile (BNot (BEq Z O))
                      (CSeq (CAsgn Y (AMult Y Z))
                            (CAsgn Z (AMinus Z (S O))))))
        : com *)
Set Printing Notations.

Print example_bexp.
(* ===> example_bexp = <{(true && ~ (X <= 4))}> *)

Set Printing Coercions.
Print example_bexp.
(* ===> example_bexp = <{(true && ~ (AId X <= ANum 4))}> *)

Print fact_in_coq.
(* ===>
  fact_in_coq =
  <{ Z := (AId X);
     Y := (ANum 1);
     while ~ (AId Z) = (ANum 0) do
       Y := (AId Y) * (AId Z);
       Z := (AId Z) - (ANum 1)
     end }>
       : com *)
Unset Printing Coercions.

(* ================================================================= *)
(** ** [Locate] Again *)

(* ----------------------------------------------------------------- *)
(** *** Finding identifiers *)

(** When used with an identifier, the [Locate] prints the full path to
    every value in scope with the same name.  This is useful to
    troubleshoot problems due to variable shadowing. *)
Locate aexp.
(* ===>
     Inductive LF.Imp.aexp
     Inductive LF.Imp.AExp.aexp
       (shorter name to refer to it in current context is AExp.aexp)
     Inductive LF.Imp.aevalR_division.aexp
       (shorter name to refer to it in current context is aevalR_division.aexp)
     Inductive LF.Imp.aevalR_extended.aexp
       (shorter name to refer to it in current context is aevalR_extended.aexp)
*)
(* ----------------------------------------------------------------- *)
(** *** Finding notations *)

(** When faced with an unknown notation, you can use [Locate] with a
    string containing one of its symbols to see its possible
    interpretations. *)
Locate "&&".
(* ===>
    Notation
      "x && y" := BAnd x y (default interpretation)
      "x && y" := andb x y : bool_scope (default interpretation)
*)
Locate ";".
(* ===>
    Notation
      "x '|->' v ';' m" := update m x v (default interpretation)
      "x ; y" := CSeq x y : com_scope (default interpretation)
      "x '!->' v ';' m" := t_update m x v (default interpretation)
      "[ x ; y ; .. ; z ]" := cons x (cons y .. (cons z nil) ..) : list_scope
      (default interpretation) *)

Locate "while".
(* ===>
    Notation
      "'while' x 'do' y 'end'" :=
          CWhile x y : com_scope (default interpretation)
*)

(* ================================================================= *)
(** ** More Examples *)

(* ----------------------------------------------------------------- *)
(** *** Assignment: *)

Definition plus2 : com :=
  <{ X := X + 2 }>.

Definition XtimesYinZ : com :=
  <{ Z := X * Y }>.

(* ----------------------------------------------------------------- *)
(** *** Loops *)

Definition subtract_slowly_body : com :=
  <{ Z := Z - 1 ;
     X := X - 1 }>.

Definition subtract_slowly : com :=
  <{ while X <> 0 do
       subtract_slowly_body
     end }>.

Definition subtract_3_from_5_slowly : com :=
  <{ X := 3 ;
     Z := 5 ;
     subtract_slowly }>.

(* ----------------------------------------------------------------- *)
(** *** An infinite loop: *)

Definition loop : com :=
  <{ while true do
       skip
     end }>.

(* ################################################################# *)
(** * Evaluating Commands *)

(** Next we need to define what it means to evaluate an Imp command.
    The fact that [while] loops don't necessarily terminate makes
    defining an evaluation function tricky... *)

(* ================================================================= *)
(** ** Evaluation as a Function (Failed Attempt) *)

(** Here's an attempt at defining an evaluation function for commands
    (with a bogus [while] case). *)

(* Fixpoint ceval_fun_no_while (st : state) (c : com) : state := *)
(*   match c with *)
(*     | <{ skip }> => *)
(*         st *)
(*     | <{ x := a }> => *)
(*         (x !-> aeval st a ; st) *)
(*     | <{ c1 ; c2 }> => *)
(*         let st' := ceval_fun_no_while st c1 in *)
(*         ceval_fun_no_while st' c2 *)
(*     | <{ if b then c1 else c2 end}> => *)
(*         if (beval st b) *)
(*           then ceval_fun_no_while st c1 *)
(*           else ceval_fun_no_while st c2 *)
(*     | <{ while b do c end }> => *)
(*         st  (* bogus *) *)
(*   end. *)

(** In a more conventional functional programming language like OCaml or
    Haskell we could add the [while] case as follows:

        Fixpoint ceval_fun (st : state) (c : com) : state :=
          match c with
            ...
            | <{ while b do c end}> =>
                if (beval st b)
                  then ceval_fun st <{c ; while b do c end}>
                  else st
          end.

    Coq doesn't accept such a definition ("Error: Cannot guess
    decreasing argument of fix") because the function we want to
    define is not guaranteed to terminate. Indeed, it _doesn't_ always
    terminate: for example, the full version of the [ceval_fun]
    function applied to the [loop] program above would never
    terminate. Since Coq aims to be not just a functional programming
    language but also a consistent logic, any potentially
    non-terminating function needs to be rejected.

    Here is an example showing what would go wrong if Coq allowed
    non-terminating recursive functions:

         Fixpoint loop_false (n : nat) : False := loop_false n.

    That is, propositions like [False] would become provable
    ([loop_false 0] would be a proof of [False]), which would be
    a disaster for Coq's logical consistency.

    Thus, because it doesn't terminate on all inputs, [ceval_fun]
    cannot be written in Coq -- at least not without additional tricks
    and workarounds (see chapter [ImpCEvalFun] if you're curious
    about those). *)

(* ================================================================= *)
(** ** Evaluation as a Relation *)

(** Here's a better way: define [ceval] as a _relation_ rather than a
    _function_ -- i.e., make its result a [Prop] rather than a
    [state], similar to what we did for [aevalR] above. *)

(** This is an important change.  Besides freeing us from awkward
    workarounds, it gives us a ton more flexibility in the definition.
    For example, if we add nondeterministic features like [any] to the
    language, we want the definition of evaluation to be
    nondeterministic -- i.e., not only will it not be total, it will
    not even be a function! *)

(** We'll use the notation [st =[ c ]=> st'] for the [ceval] relation:
    [st =[ c ]=> st'] means that executing program [c] in a starting
    state [st] results in an ending state [st'].  This can be
    pronounced "[c] takes state [st] to [st']". *)

(* ----------------------------------------------------------------- *)
(** *** Operational Semantics *)

(** Here is an informal definition of evaluation, presented as inference
    rules for readability:

                           -----------------                            (E_Skip)
                           st =[ skip ]=> st

                           aeval st a = n
                   -------------------------------                      (E_Asgn)
                   st =[ x := a ]=> (x !-> n ; st)

                           st  =[ c1 ]=> st'
                           st' =[ c2 ]=> st''
                         ---------------------                           (E_Seq)
                         st =[ c1;c2 ]=> st''

                          beval st b = true
                           st =[ c1 ]=> st'
                --------------------------------------               (E_IfTrue)
                st =[ if b then c1 else c2 end ]=> st'

                         beval st b = false
                           st =[ c2 ]=> st'
                --------------------------------------              (E_IfFalse)
                st =[ if b then c1 else c2 end ]=> st'

                         beval st b = false
                    -----------------------------                 (E_WhileFalse)
                    st =[ while b do c end ]=> st

                          beval st b = true
                           st =[ c ]=> st'
                  st' =[ while b do c end ]=> st''
                  --------------------------------                 (E_WhileTrue)
                  st  =[ while b do c end ]=> st''
*)

(** Here is the formal definition.  Make sure you understand
    how it corresponds to the inference rules. *)

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
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> Some st' ->
      st =[ if b then c1 else c2 end]=> Some st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> Some st' ->
      st =[ if b then c1 else c2 end]=> Some st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> Some st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> Some st' ->
      st' =[ while b do c end ]=> Some st'' ->
      st  =[ while b do c end ]=> Some st''

  where "st =[ c ]=> st'" := (ceval c st st').

(** The cost of defining evaluation as a relation instead of a
    function is that we now need to construct a _proof_ that some
    program evaluates to some result state, rather than just letting
    Coq's computation mechanism do it for us. *)

Example ceval_example1:
  empty_st =[
     X := 2;
     if (X <= 1)
       then Y := 3
       else Z := 4
     end
  ]=> Some (Z !-> 4 ; X !-> 2).
Proof.
  (* We must supply the intermediate state *)
  apply E_Seq with (X !-> 2).
  - (* assignment command *)
    apply E_Asgn; eauto.
  - (* if command *)
    apply E_IfFalse.
    + reflexivity.
    + apply E_Asgn; eauto.
Qed.

(** **** Exercise: 2 stars, standard (ceval_example2) *)
Example ceval_example2:
  empty_st =[
    X := 0;
    Y := 1;
    Z := 2
  ]=> Some (Z !-> 2 ; Y !-> 1 ; X !-> 0).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

Set Printing Implicit.
Check @ceval_example2.

(** **** Exercise: 3 stars, standard, optional (pup_to_n)

    Write an Imp program that sums the numbers from [1] to [X]
    (inclusive: [1 + 2 + ... + X]) in the variable [Y].  Your program
    should update the state as shown in theorem [pup_to_2_ceval],
    which you can reverse-engineer to discover the program you should
    write.  The proof of that theorem will be somewhat lengthy. *)

Definition pup_to_n : com
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Theorem pup_to_2_ceval :
  (X !-> 2) =[
    pup_to_n
  ]=> Some (X !-> 0 ; Y !-> 3 ; X !-> 1 ; Y !-> 2 ; Y !-> 0 ; X !-> 2).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Determinism of Evaluation *)

(** Changing from a computational to a relational definition of
    evaluation is a good move because it frees us from the artificial
    requirement that evaluation should be a total function.  But it
    also raises a question: Is the second definition of evaluation
    really a partial _function_?  Or is it possible that, beginning from
    the same state [st], we could evaluate some command [c] in
    different ways to reach two different output states [st'] and
    [st'']?

    In fact, this cannot happen: [ceval] _is_ a partial function: *)

Theorem ceval_deterministic: forall c st st1 st2,
     st =[ c ]=> st1  ->
     st =[ c ]=> st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  induction E1; intros st2 E2; inversion E2; subst; eauto; try nia; try firstorder.
  - (* E_Seq *)
    eapply IHE1_1 in H1. inversion H1; subst.
    eapply IHE1_2; eauto.
  - (* E_IfFalse, b evaluates to true (contradiction) *)
    rewrite H in H5. discriminate.
  - (* E_IfFalse, b evaluates to true (contradiction) *)
    rewrite H in H5. discriminate.    
  - (* E_WhileFalse, b evaluates to true (contradiction) *)
    rewrite H in H2. discriminate.
  - (* E_WhileTrue, b evaluates to false (contradiction) *)
    rewrite H in H4. discriminate.
  - (* E_WhileTrue, b evaluates to true *)
    eapply IHE1_1 in H3. inversion H3; subst.
    apply IHE1_2. eauto.
Qed.

(* ################################################################# *)
(** * Reasoning About Imp Programs *)

(** We'll get into more systematic and powerful techniques for
    reasoning about Imp programs in _Programming Language
    Foundations_, but we can already do a few things (albeit in a
    somewhat low-level way) just by working with the bare definitions.
    This section explores some examples. *)

Theorem plus2_spec : forall st n st',
  st X = n ->
  st =[ plus2 ]=> Some st' ->
  st' X = n + 2.
Proof.
  intros st n st' HX Heval.

  (** Inverting [Heval] essentially forces Coq to expand one step of
      the [ceval] computation -- in this case revealing that [st']
      must be [st] extended with the new value of [X], since [plus2]
      is an assignment. *)

  inversion Heval. subst. clear Heval. simpl.
  apply t_update_eq.  Qed.

(** **** Exercise: 3 stars, standard, optional (XtimesYinZ_spec)

    State and prove a specification of [XtimesYinZ]. *)

(* FILL IN HERE *)

(* Do not modify the following line: *)
Definition manual_grade_for_XtimesYinZ_spec : option (nat*string) := None.
(** [] *)

(** **** Exercise: 3 stars, standard, especially useful (loop_never_stops) *)
Theorem loop_never_stops : forall st st',
  ~(st =[ loop ]=> st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember <{ while true do skip end }> as loopdef
           eqn:Heqloopdef.

  (** Proceed by induction on the assumed derivation showing that
      [loopdef] terminates.  Most of the cases are immediately
      contradictory and so can be solved in one step with
      [discriminate]. *)

  (* FILL IN HERE *) Admitted.
(** [] *)
