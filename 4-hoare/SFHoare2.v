(** * Hoare2: Hoare Logic, Part II *)

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
Set Default Goal Selector "!".

Definition FILL_IN_HERE := <{True}>.

(* ################################################################# *)
(** * Decorated Programs *)

(** The beauty of Hoare Logic is that it is _structure-guided_: the
    structure of proofs exactly follows the structure of programs.

    We can record the essential ideas of a Hoare-logic proof --
    omitting low-level calculational details -- by "decorating" a
    program with appropriate assertions on each of its commands.

    Such a _decorated program_ carries within itself an argument for
    its own correctness. *)

(** For example, consider the program:

    X := m;
    Z := p;
    while X <> 0 do
      Z := Z - 1;
      X := X - 1
    end
*)
(** Here is one possible specification for this program, in the
    form of a Hoare triple:

    {{ True }}
    X := m;
    Z := p;
    while X <> 0 do
      Z := Z - 1;
      X := X - 1
    end
    {{ Z = p - m }}
*)
(** (Note the _parameters_ [m] and [p], which stand for
   fixed-but-arbitrary numbers.  Formally, they are simply Coq
   variables of type [nat].) *)

(** Here is a decorated version of this program, embodying a
    proof of this specification:

    {{ True }} ->>
    {{ m = m }}
      X := m
                         {{ X = m }} ->>
                         {{ X = m /\ p = p }};
      Z := p;
                         {{ X = m /\ Z = p }} ->>
                         {{ Z - X = p - m }}
      while X <> 0 do
                         {{ Z - X = p - m /\ X <> 0 }} ->>
                         {{ (Z - 1) - (X - 1) = p - m }}
        Z := Z - 1
                         {{ Z - (X - 1) = p - m }};
        X := X - 1
                         {{ Z - X = p - m }}
      end
    {{ Z - X = p - m /\ ~ (X <> 0) }} ->>
    {{ Z = p - m }}
*)

(** Concretely, a decorated program consists of the program's text
    interleaved with assertions (sometimes multiple assertions
    separated by implications). *)

(** A decorated program can be viewed as a compact representation of a
    proof in Hoare Logic: the assertions surrounding each command
    specify the Hoare triple to be proved for that part of the program
    using one of the Hoare Logic rules, and the structure of the
    program itself shows how to assemble all these individual steps
    into a proof for the whole program. *)

(** Our goal is to verify such decorated programs "mostly
    automatically."  But, before we can verify anything, we need to be
    able to _find_ a proof for a given specification, and for this we
    need to discover the right assertions. This can be done in an
    almost mechanical way, with the exception of finding loop
    invariants. In the remainder of this section we explain in detail
    how to construct decorations for several short programs, all of
    which are loop-free or have simple loop invariants. We'll return
    to finding more interesting loop invariants later in the chapter. *)

(* ================================================================= *)
(** ** Example: Swapping *)

(** Consider the following program, which swaps the values of two
    variables using addition and subtraction (instead of by assigning
    to a temporary variable).

       {X = m /\ Y = n}
       {X+Y = m+n /\ Y = n}
       X := X + Y;
       {X = m+n /\ Y = n}
       {X = m+n /\ X-Y = m}
       Y := X - Y;
       {X = m+n /\ Y = m}
       {X-Y = n /\ Y = m}
       X := X - Y
       {X = n /\ Y = m}

    We can give a proof, in the form of decorations, that this program is
    correct -- i.e., it really swaps [X] and [Y] -- as follows.

    (1)    {{ X = m /\ Y = n }} ->>
    (2)    {{ (X + Y) - ((X + Y) - Y) = n /\ (X + Y) - Y = m }}
             X := X + Y
    (3)                     {{ X - (X - Y) = n /\ X - Y = m }};
             Y := X - Y
    (4)                     {{ X - Y = n /\ Y = m }};
             X := X - Y
    (5)    {{ X = n /\ Y = m }}

    The decorations can be constructed as follows:

      - We begin with the undecorated program (the unnumbered lines).

      - We add the specification -- i.e., the outer precondition (1)
        and postcondition (5). In the precondition, we use parameters
        [m] and [n] to remember the initial values of variables [X]
        and [Y] so that we can refer to them in the postcondition (5).

      - We work backwards, mechanically, starting from (5) and
        proceeding until we get to (2). At each step, we obtain the
        precondition of the assignment from its postcondition by
        substituting the assigned variable with the right-hand-side of
        the assignment. For instance, we obtain (4) by substituting
        [X] with [X - Y] in (5), and we obtain (3) by substituting [Y]
        with [X - Y] in (4).

    Finally, we verify that (1) logically implies (2) -- i.e., that
    the step from (1) to (2) is a valid use of the law of
    consequence -- by doing a bit of high-school algebra.
 *)

(* ================================================================= *)
(** ** Example: Simple Conditionals *)

(** Here is a simple decorated program using conditionals:

      (1)   {{ True }}
              if X <= Y then
      (2)                    {{ True /\ X <= Y }} ->>
      (3)                    {{ (Y - X) + X = Y \/ (Y - X) + Y = X }}
                Z := Y - X
      (4)                    {{ Z + X = Y \/ Z + Y = X }}
              else
      (5)                    {{ True /\ ~(X <= Y) }} ->>
      (6)                    {{ (X - Y) + X = Y \/ (X - Y) + Y = X }}
                Z := X - Y
      (7)                    {{ Z + X = Y \/ Z + Y = X }}
              end
      (8)   {{ Z + X = Y \/ Z + Y = X }}

These decorations can be constructed as follows:

  - We start with the outer precondition (1) and postcondition (8).

  - Following the format dictated by the [hoare_if] rule, we copy the
    postcondition (8) to (4) and (7). We conjoin the precondition (1)
    with the guard of the conditional to obtain (2). We conjoin (1)
    with the negated guard of the conditional to obtain (5).

  - In order to use the assignment rule and obtain (3), we substitute
    [Z] by [Y - X] in (4). To obtain (6) we substitute [Z] by [X - Y]
    in (7).

  - Finally, we verify that (2) implies (3) and (5) implies (6). Both
    of these implications crucially depend on the ordering of [X] and
    [Y] obtained from the guard. For instance, knowing that [X <= Y]
    ensures that subtracting [X] from [Y] and then adding back [X]
    produces [Y], as required by the first disjunct of (3). Similarly,
    knowing that [~ (X <= Y)] ensures that subtracting [Y] from [X]
    and then adding back [Y] produces [X], as needed by the second
    disjunct of (6). Note that [n - m + m = n] does _not_ hold for
    arbitrary natural numbers [n] and [m] (for example, [3 - 5 + 5 =
    5]). *)

(** **** Exercise: 2 stars, standard, optional (if_minus_plus_reloaded)

    N.b.: Although this exercise is marked optional, it is an
    excellent warm-up for the (non-optional) [if_minus_plus_correct]
    exercise below!

    Fill in valid decorations for the following program: *)
(*
  {{ True }}
    if X <= Y then
              {{                         }} ->>
              {{                         }}
      Z := Y - X
              {{                         }}
    else
              {{                         }} ->>
              {{                         }}
      Y := X + Z
              {{                         }}
    end
  {{ Y = X + Z }}
*)
(**
    Briefly justify each use of [->>].
*)

(** [] *)

(* ================================================================= *)
(** ** Example: Reduce to Zero *)

(** Here is a [while] loop that is so simple that [True] suffices
    as a loop invariant.

        (1)    {{ True }}
                 while X <> 0 do
        (2)                  {{ True /\ X <> 0 }} ->>
        (3)                  {{ True }}
                   X := X - 1
        (4)                  {{ True }}
                 end
        (5)    {{ True /\ ~(X <> 0) }} ->>
        (6)    {{ X = 0 }}

   The decorations can be constructed as follows:

     - Start with the outer precondition (1) and postcondition (6).

     - Following the format dictated by the [hoare_while] rule, we copy
       (1) to (4). We conjoin (1) with the guard to obtain (2). We also
       conjoin (1) with the negation of the guard to obtain (5).

     - Because the final postcondition (6) does not syntactically match (5),
       we add an implication between them.

     - Using the assignment rule with assertion (4), we trivially substitute
       and obtain assertion (3).

     - We add the implication between (2) and (3).

   Finally we check that the implications do hold; both are trivial. *)

(* ================================================================= *)
(** ** Example: Division *)

(** Let's do one more example of simple reasoning about a loop.

    The following Imp program calculates the integer quotient and
    remainder of parameters [m] and [n].

       X := m;
       Y := 0;
       while n <= X do
         X := X - n;
         Y := Y + 1
       end;

    If we replace [m] and [n] by concrete numbers and execute the program, it
    will terminate with the variable [X] set to the remainder when [m]
    is divided by [n] and [Y] set to the quotient. *)

(** In order to give a specification to this program we need to
    remember that dividing [m] by [n] produces a remainder [X] and a
    quotient [Y] such that [n * Y + X = m /\ X < n].

    It turns out that we get lucky with this program and don't have to
    think very hard about the loop invariant: the loop invariant is just
    the first conjunct, [n * Y + X = m], and we can use this to
    decorate the program.

      (1)  {{ True }} ->>
      (2)  {{ n * 0 + m = m }}
             X := m;
      (3)                     {{ n * 0 + X = m }}
             Y := 0;
      (4)                     {{ n * Y + X = m }}
             while n <= X do
      (5)                     {{ n * Y + X = m /\ n <= X }} ->>
      (6)                     {{ n * (Y + 1) + (X - n) = m }}
               X := X - n;
      (7)                     {{ n * (Y + 1) + X = m }}
               Y := Y + 1
      (8)                     {{ n * Y + X = m }}
             end
      (9)  {{ n * Y + X = m /\ ~ (n <= X) }} ->>
     (10)  {{ n * Y + X = m /\ X < n }}

    Assertions (4), (5), (8), and (9) are derived mechanically from
    the loop invariant and the loop's guard.  Assertions (8), (7), and (6)
    are derived using the assignment rule going backwards from (8)
    to (6).  Assertions (4), (3), and (2) are again backwards
    applications of the assignment rule.

    Now that we've decorated the program it only remains to check that
    the uses of the consequence rule are correct -- i.e., that (1)
    implies (2), that (5) implies (6), and that (9) implies (10). This
    is indeed the case:
      - (1) ->> (2):  trivial, by algebra.
      - (5) ->> (6):  because [n <= X], we are guaranteed that the
        subtraction in (6) does not get zero-truncated.  We can
        therefore rewrite (6) as [n * Y + n + X - n] and cancel the
        [n]s, which results in the left conjunct of (5).
      - (9) ->> (10):  if [~ (n <= X)] then [X < n].  That's straightforward
        from high-school algebra.
    So, we have a valid decorated program. *)

(* ================================================================= *)
(** ** From Decorated Programs to Formal Proofs *)

(** From an informal proof in the form of a decorated program, it is
    "easy in principle" to read off a formal proof using the Coq
    theorems corresponding to the Hoare Logic rules, but these proofs
    can be a bit long and fiddly. *)

(** Note that we do _not_ unfold the definition of [valid_hoare_triple]
    anywhere in this proof: the point of the game we're playing now
    is to use the Hoare rules as a self-contained logic for reasoning
    about programs. *)

(** For example... *)
Definition reduce_to_zero : com :=
  <{ while X <> 0 do
       X := X - 1
     end }>.

Theorem reduce_to_zero_correct' :
  {{True}}
    reduce_to_zero
  {{X = 0}}.
Proof.
  unfold reduce_to_zero.
  (* First we need to transform the postcondition so
     that hoare_while will apply. *)
  eapply hoare_consequence_post.
  - apply hoare_while.
    + (* Loop body preserves loop invariant *)
      (* Massage precondition so [hoare_asgn] applies *)
      eapply hoare_consequence_pre.
      * apply hoare_asgn.
      * (* Proving trivial implication (2) ->> (3) *)
        unfold assertion_sub, "->>". simpl. intros.
        eauto.
  - (* Loop invariant and negated guard imply post *)
    intros st [Inv GuardFalse].
    unfold bassertion in GuardFalse. simpl in GuardFalse.
    rewrite not_true_iff_false in GuardFalse.
    rewrite negb_false_iff in GuardFalse.
    apply eqb_eq in GuardFalse.
    apply GuardFalse.
Qed.

(** In [Hoare] we introduced a series of tactics named
    [assertion_auto] to automate proofs involving assertions.

    The following declaration introduces a more sophisticated tactic
    that will help with proving assertions throughout the rest of this
    chapter.  You don't need to understand the details, but briefly:
    it uses [split] repeatedly to turn all the conjunctions into
    separate subgoals, tries to use several theorems about booleans
    and (in)equalities, then uses [eauto] and [lia] to finish off as
    many subgoals as possible. What's left after [verify_assertion] does
    its thing should be just the "interesting parts" of the proof --
    which, if we're lucky, might be nothing at all! *)

Ltac verify_assertion :=
  repeat split;
  simpl;
  unfold assert_implies;
  unfold bassertion in *; unfold beval in *; unfold aeval in *;
  unfold assertion_sub; intros;
  repeat (simpl in *;
          rewrite t_update_eq ||
          (try rewrite t_update_neq;
          [| (intro X; inversion X; fail)]));
  simpl in *;
  repeat match goal with [H : _ /\ _ |- _] =>
                         destruct H end;
  repeat rewrite not_true_iff_false in *;
  repeat rewrite not_false_iff_true in *;
  repeat rewrite negb_true_iff in *;
  repeat rewrite negb_false_iff in *;
  repeat rewrite eqb_eq in *;
  repeat rewrite eqb_neq in *;
  repeat rewrite leb_iff in *;
  repeat rewrite leb_iff_conv in *;
  try subst;
  simpl in *;
  repeat
    match goal with
      [st : state |- _] =>
        match goal with
        | [H : st _ = _ |- _] =>
            rewrite -> H in *; clear H
        | [H : _ = st _ |- _] =>
            rewrite <- H in *; clear H
        end
    end;
  try eauto;
  try nia.

(** This makes it pretty easy to verify [reduce_to_zero]: *)

Theorem reduce_to_zero_correct''' :
  {{True}}
    reduce_to_zero
  {{X = 0}}.
Proof.
  unfold reduce_to_zero.
  eapply hoare_consequence_post.
  - apply hoare_while.
    + eapply hoare_consequence_pre.
      * apply hoare_asgn.
      * verify_assertion.
  - verify_assertion.
Qed.

Lemma foo: forall (m n: nat),
  {{ True }}
  <{
       X := m;
       Y := 0;
       while n <= X do
         X := X - n;
         Y := Y + 1
       end
  }>
  {{ X = #modulo m n /\ Y = #div m n }}.
Proof.
  intros.
  eapply hoare_seq.
  - eapply hoare_seq.
    + eapply hoare_consequence_post.
      * eapply hoare_while
          with (P:= {{ X + Y*n = m }}).
        eapply hoare_seq.
        -- eapply hoare_asgn.
        -- eapply hoare_consequence_pre.
           ++ eapply hoare_asgn.
           ++ verify_assertion.
      * verify_assertion.
        -- admit.
        -- admit.
    + eapply hoare_asgn.
  - eapply hoare_consequence_pre.
    + eapply hoare_asgn.
    + verify_assertion.
Admitted.

(******
   Automation based on Weakest Precondition
 ******)

Theorem hoare_if_wp : forall P1 P2 Q (b:bexp) c1 c2,
    {{ P1 }} c1 {{ Q }} ->
    {{ P2 }} c2 {{ Q }} ->
    {{ (b -> P1) /\ (~ b -> P2) }} if b then c1 else c2 end {{ Q }}.
Proof.
  intros P1 P2 Q b c1 c2 HTrue HFalse st st' HE [HP1 HP2].
  inversion HE; subst; eauto.
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

Hint Resolve hoare_div : hoare.

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
    | [H: (_ =? _) = true |- _] => eapply eqb_eq in H
    | [H: (_ =? _) = false |- _] => eapply eqb_neq in H
    end;
  repeat (
    try rewrite -> eqb_eq in *;
    try rewrite -> leb_le in *;
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


(** An example [decorated] program that decrements [X] to [0]: *)

Example ex_while : com :=
  <{
    while X <> 0
    do
      X := X - 1
    end
  }>.

(** For example: *)

Theorem while_correct :
  {{ True }} ex_while  {{ X = 0 }}.
Proof.
  unfold ex_while.
  hauto_while {{ True }}.
Qed.

(** Similarly, here is the formal decorated program for the "swapping
    by adding and subtracting" example that we saw earlier. *)

Definition ex_swap : com :=
  <{
    X := X + Y;
    Y := X - Y;
    X := X - Y
  }>.
          
Theorem swap_correct: forall (m n: nat),
    {{ X = m /\ Y = n }} ex_swap {{ X = n /\ Y = m }}.
Proof.
  unfold ex_swap.
  hauto.
Qed.

(** And here is the formal decorated version of the "positive
    difference" program from earlier: *)

Definition ex_positive_difference :=
  <{
    if X <= Y then
      Z := Y - X
    else
      Z := X - Y
    end
  }>.

Theorem positive_difference_correct :
    {{True}}
      ex_positive_difference
    {{Z + X = Y \/ Z + Y = X}}.
Proof. unfold ex_positive_difference. hauto. Qed.

(** **** Exercise: 2 stars, standard, especially useful (if_minus_plus_correct)

    Here is a skeleton of the formal decorated version of the
    [if_minus_plus] program that we saw earlier.  Replace all
    occurrences of [FILL_IN_HERE] with appropriate assertions and fill
    in the proof (which should be just as straightforward as in the
    examples above). *)

Definition ex_if_minus_plus :=
  <{
  if (X <= Y) then
    Z := Y - X
  else
    Y := X + Z
  end
  }>.

Theorem if_minus_plus_correct :
  {{True}}
    ex_if_minus_plus
  {{ Y = X + Z}}.
Proof.
  unfold ex_if_minus_plus. hauto.
Qed.

(** **** Exercise: 2 stars, standard, optional (div_mod_outer_triple_valid)

    Fill in appropriate assertions for the division program from above. *)

Definition ex_div_mod (a b : nat) :=
  <{
    X := a;
    Y := 0;
    while b <= X do
      X := X - b;
      Y := Y + 1
    end
  }>.

Theorem div_mod_outer_triple_valid : forall (a b: nat),
    {{ b > 0 }}
      ex_div_mod a b
    {{ X = #modulo a b /\ Y = #div a b }}.
Proof.
  unfold ex_div_mod. hauto.
  - hauto_while {{a = b * Y + X}}.
    hauto_vc.
    rewrite <-Div0.add_mod_idemp_l, mul_comm, Div0.mod_mul, mod_small; eauto.
    hexploit (div_le_lower_bound (st Y * b + st X) b (st Y)); try nia. intros.
    hexploit (Div0.div_lt_upper_bound (st Y * b + st X) b (1 + st Y)); nia.
  - hauto_vc.
Qed.
(** [] *)

(* ################################################################# *)
(** * Finding Loop Invariants *)

(** Once the outermost precondition and postcondition are
    chosen, the only creative part of a verifying program using Hoare
    Logic is finding the right loop invariants.  The reason this is
    difficult is the same as the reason that inductive mathematical
    proofs are:

    - Strengthening a _loop invariant_ means that you have a stronger
      assumption to work with when trying to establish the
      postcondition of the loop body, but it also means that the loop
      body's postcondition is stronger and thus harder to prove.

    - Similarly, strengthening an _induction hypothesis_ means that
      you have a stronger assumption to work with when trying to
      complete the induction step of the proof, but it also means that
      the statement being proved inductively is stronger and thus
      harder to prove.

    This section explains how to approach the challenge of finding
    loop invariants through a series of examples and exercises. *)

(* ================================================================= *)
(** ** Example: Slow Subtraction *)

(** The following program subtracts the value of [X] from the value of
    [Y] by repeatedly decrementing both [X] and [Y].  We want to verify its
    correctness with respect to the pre- and postconditions shown:

           {{ X = m /\ Y = n }}
             while X <> 0 do
               Y := Y - 1;
               X := X - 1
             end
           {{ Y = n - m }}
*)

(** To verify this program, we need to find an invariant [Inv] for the
    loop.  As a first step we can leave [Inv] as an unknown and build a
    _skeleton_ for the proof by applying the rules for local
    consistency, working from the end of the program to the beginning,
    as usual, and without any thinking at all yet. *)

(** This leads to the following skeleton:

        (1)    {{ X = m /\ Y = n }}  ->>                   (a)
        (2)    {{ Inv }}
                 while X <> 0 do
        (3)              {{ Inv /\ X <> 0 }}  ->>          (c)
        (4)              {{ Inv [X |-> X-1] [Y |-> Y-1] }}
                   Y := Y - 1;
        (5)              {{ Inv [X |-> X-1] }}
                   X := X - 1
        (6)              {{ Inv }}
                 end
        (7)    {{ Inv /\ ~ (X <> 0) }}  ->>                (b)
        (8)    {{ Y = n - m }}
*)
(** By examining this skeleton, we can see that any valid [Inv] will
    have to respect three conditions:
    - (a) it must be _weak_ enough to be implied by the loop's
      precondition, i.e., (1) must imply (2);
    - (b) it must be _strong_ enough to imply the program's postcondition,
      i.e., (7) must imply (8);
    - (c) it must be _preserved_ by a single iteration of the loop, assuming
      that the loop guard also evaluates to true, i.e., (3) must imply (4). *)

(** These conditions are actually independent of the particular
    program and specification we are considering: every loop
    invariant has to satisfy them.

    One way to find a loop invariant that simultaneously satisfies these
    three conditions is by using an iterative process: start with a
    "candidate" invariant (e.g., a guess or a heuristic choice) and
    check the three conditions above; if any of the checks fails, try
    to use the information that we get from the failure to produce
    another -- hopefully better -- candidate invariant, and repeat.

    For instance, in the reduce-to-zero example above, we saw that,
    for a very simple loop, choosing [True] as a loop invariant did the
    job.  Maybe it will work here too.  To find out, let's try
    instantiating [Inv] with [True] in the skeleton above and
    see what we get...

        (1)    {{ X = m /\ Y = n }} ->>                    (a - OK)
        (2)    {{ True }}
                 while X <> 0 do
        (3)                   {{ True /\ X <> 0 }} ->>     (c - OK)
        (4)                   {{ True }}
                   Y := Y - 1;
        (5)                   {{ True }}
                   X := X - 1
        (6)                   {{ True }}
                 end
        (7)    {{ True /\ ~(X <> 0) }} ->>                 (b - WRONG!)
        (8)    {{ Y = n - m }}

    While conditions (a) and (c) are trivially satisfied,
    (b) is wrong: it is not the case that [True /\ X = 0] (7)
    implies [Y = n - m] (8).  In fact, the two assertions are
    completely unrelated, so it is very easy to find a counterexample
    to the implication (say, [Y = X = m = 0] and [n = 1]).

    If we want (b) to hold, we need to strengthen the loop invariant so
    that it implies the postcondition (8).  One simple way to do
    this is to let the loop invariant _be_ the postcondition.  So let's
    return to our skeleton, instantiate [Inv] with [Y = n - m], and
    try checking conditions (a) to (c) again.

    (1)    {{ X = m /\ Y = n }} ->>                        (a - WRONG!)
    (2)    {{ Y = n - m }}
             while X <> 0 do
    (3)                     {{ Y = n - m /\ X <> 0 }} ->>  (c - WRONG!)
    (4)                     {{ Y - 1 = n - m }}
               Y := Y - 1;
    (5)                     {{ Y = n - m }}
               X := X - 1
    (6)                     {{ Y = n - m }}
             end
    (7)    {{ Y = n - m /\ ~(X <> 0) }} ->>                (b - OK)
    (8)    {{ Y = n - m }}

    This time, condition (b) holds trivially, but (a) and (c) are
    broken. Condition (a) requires that (1) [X = m /\ Y = n]
    implies (2) [Y = n - m].  If we substitute [Y] by [n] we have to
    show that [n = n - m] for arbitrary [m] and [n], which is not
    the case (for instance, when [m = n = 1]).  Condition (c) requires
    that [n - m - 1 = n - m], which fails, for instance, for [n = 1]
    and [m = 0]. So, although [Y = n - m] holds at the end of the loop,
    it does not hold from the start, and it doesn't hold on each
    iteration; it is not a correct loop invariant.

    This failure is not very surprising: the variable [Y] changes
    during the loop, while [m] and [n] are constant, so the assertion
    we chose didn't have much chance of being a loop invariant!

    To do better, we need to generalize (7) to some statement that is
    equivalent to (8) when [X] is [0], since this will be the case
    when the loop terminates, and that "fills the gap" in some
    appropriate way when [X] is nonzero.  Looking at how the loop
    works, we can observe that [X] and [Y] are decremented together
    until [X] reaches [0].  So, if [X = 2] and [Y = 5] initially,
    after one iteration of the loop we obtain [X = 1] and [Y = 4];
    after two iterations [X = 0] and [Y = 3]; and then the loop stops.
    Notice that the difference between [Y] and [X] stays constant
    between iterations: initially, [Y = n] and [X = m], and the
    difference is always [n - m].  So let's try instantiating [Inv] in
    the skeleton above with [Y - X = n - m].

    (1)    {{ X = m /\ Y = n }} ->>                            (a - OK)
    (2)    {{ Y - X = n - m }}
             while X <> 0 do
    (3)                    {{ Y - X = n - m /\ X <> 0 }} ->>   (c - OK)
    (4)                    {{ (Y - 1) - (X - 1) = n - m }}
               Y := Y - 1;
    (5)                    {{ Y - (X - 1) = n - m }}
               X := X - 1
    (6)                    {{ Y - X = n - m }}
             end
    (7)    {{ Y - X = n - m /\ ~(X <> 0) }} ->>                (b - OK)
    (8)    {{ Y = n - m }}

    Success!  Conditions (a), (b) and (c) all hold now.  (To
    verify (c), we need to check that, under the assumption that
    [X <> 0], we have [Y - X = (Y - 1) - (X - 1)]; this holds for all
    natural numbers [X] and [Y].)

    Here is the final version of the decorated program: *)

Example ex_subtract_slowly (m : nat) (n : nat) :=
  <{
    while X <> 0 do
       Y := Y - 1;
       X := X - 1
    end
  }>.

Theorem subtract_slowly_correct : forall (m n: nat),
  {{ X = m /\  Y = n }}
    ex_subtract_slowly m n
  {{ Y = n - m }}.
Proof.
  unfold ex_subtract_slowly. intros.
  hauto_while {{ Y - X = n - m }}.
Qed.

(* ================================================================= *)
(** ** Exercise: Slow Assignment *)

(** **** Exercise: 2 stars, standard (slow_assignment)

    A roundabout way of assigning a number currently stored in [X] to
    the variable [Y] is to start [Y] at [0], then decrement [X] until
    it hits [0], incrementing [Y] at each step. Here is a program that
    implements this idea.  Fill in decorations and prove the decorated
    program correct. (The proof should be very simple.) *)

Example ex_slow_assignment :=
  <{
      Y := 0;
      while X <> 0 do
         X := X - 1;
         Y := Y + 1
      end
  }>.

Theorem slow_assignment_correct : forall (m: nat),
    {{ X = m }}
      ex_slow_assignment
    {{ Y = m }}.
Proof. (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Example: Parity *)

(** Here is a cute way of computing the parity of a value initially
    stored in [X], due to Daniel Cristofani.

       {{ X = m }}
         while 2 <= X do
           X := X - 2
         end
       {{ X = parity m }}

    The [parity] function used in the specification is defined in
    Coq as follows: *)

Fixpoint parity x :=
  match x with
  | 0 => 0
  | 1 => 1
  | S (S x') => parity x'
  end.

(** The postcondition does not hold at the beginning of the loop,
    since [m = parity m] does not hold for an arbitrary [m], so we
    cannot hope to use that as a loop invariant.  To find a loop invariant
    that works, let's think a bit about what this loop does.  On each
    iteration it decrements [X] by [2], which preserves the parity of [X].
    So the parity of [X] does not change, i.e., it is invariant.  The initial
    value of [X] is [m], so the parity of [X] is always equal to the
    parity of [m]. Using [parity X = parity m] as an invariant we
    obtain the following decorated program:

      {{ X = m }} ->>                                         (a - OK)
      {{ parity X = parity m }}
        while 2 <= X do
                     {{ parity X = parity m /\ 2 <= X }} ->>  (c - OK)
                     {{ parity (X-2) = parity m }}
          X := X - 2
                     {{ parity X = parity m }}
        end
      {{ parity X = parity m /\ ~(2 <= X) }} ->>              (b - OK)
      {{ X = parity m }}

    With this loop invariant, conditions (a), (b), and (c) are all
    satisfied. For verifying (b), we observe that, when [X < 2], we
    have [parity X = X] (we can easily see this in the definition of
    [parity]).  For verifying (c), we observe that, when [2 <= X], we
    have [parity X = parity (X-2)]. *)

(** **** Exercise: 3 stars, standard, optional (parity)

    Translate the above informal decorated program into a formal one
    and prove it correct.

    Hint: There are actually several possible loop invariants that all
    lead to good proofs; one that leads to a particularly simple proof
    is [parity X = parity m] -- or more formally, using the
    [ap] operator to lift the application of the [parity] function
    into the syntax of assertions, [{{ ap parity X = parity m }}]. *)

Definition ex_parity (m:nat) :=
  <{
    while 2 <= X do
      X := X - 2
    end
  }>.

(** If you use the suggested loop invariant, you may find the following
    lemmas helpful (as well as [leb_complete] and [leb_correct]). *)

Lemma parity_ge_2 : forall x,
  2 <= x ->
  parity (x - 2) = parity x.
Proof.
  destruct x; intros; simpl.
  - reflexivity.
  - destruct x; simpl.
    + lia.
    + rewrite sub_0_r. reflexivity.
Qed.

Lemma parity_lt_2 : forall x,
  ~ 2 <= x ->
  parity x = x.
Proof.
  induction x; intros; simpl.
  - reflexivity.
  - destruct x.
    + reflexivity.
    + lia.
Qed.

Theorem parity_correct (m: nat):
  {{ X = m }}
    ex_parity m
  {{ X = #parity m }}.
Proof.
  unfold ex_parity. hauto_while {{ #parity X = #parity m }}.
  - hauto_vc. 
    destruct (st X); try firstorder; try discriminate.
    destruct n; try firstorder; try discriminate.
    simpl in *. rewrite <-H. f_equal. nia.
  - hauto_vc.
    destruct (st X); try firstorder; try discriminate.
    destruct n; try firstorder; try discriminate.
Qed.

(** [] *)

(* ================================================================= *)
(** ** Example: Finding Square Roots *)

(** The following program computes the integer square root of [X]
    by naive iteration:

    {{ X=m }}
      Z := 0;
      while (Z+1)*(Z+1) <= X do
        Z := Z+1
      end
    {{ Z*Z<=m /\ m<(Z+1)*(Z+1) }}
*)

(** As we did before, we can try to use the postcondition as a
    candidate loop invariant, obtaining the following decorated program:

    (1)  {{ X=m }} ->>               (a - second conjunct of (2) WRONG!)
    (2)  {{ 0*0 <= m /\ m<(0+1)*(0+1) }}
            Z := 0
    (3)            {{ Z*Z <= m /\ m<(Z+1)*(Z+1) }};
            while (Z+1)*(Z+1) <= X do
    (4)            {{ Z*Z<=m /\ m<(Z+1)*(Z+1)
                             /\ (Z+1)*(Z+1)<=X }} ->>   (c - WRONG!)
    (5)            {{ (Z+1)*(Z+1)<=m /\ m<((Z+1)+1)*((Z+1)+1) }}
              Z := Z+1
    (6)            {{ Z*Z<=m /\ m<(Z+1)*(Z+1) }}
            end
    (7)  {{ Z*Z<=m /\ m<(Z+1)*(Z+1) /\ ~((Z+1)*(Z+1)<=X) }} ->>  (b - OK)
    (8)  {{ Z*Z<=m /\ m<(Z+1)*(Z+1) }}

    This didn't work very well: conditions (a) and (c) both failed.
    Looking at condition (c), we see that the second conjunct of (4)
    is almost the same as the first conjunct of (5), except that (4)
    mentions [X] while (5) mentions [m]. But note that [X] is never
    assigned in this program, so we should always have [X=m]. We
    didn't propagate this information from (1) into the loop
    invariant, but we could!

    Also, we don't need the second conjunct of (8), since we can
    obtain it from the negation of the guard -- the third conjunct
    in (7) -- again under the assumption that [X=m].  This allows
    us to simplify a bit.

    So we now try [X=m /\ Z*Z <= m] as the loop invariant:

    {{ X=m }} ->>                                           (a - OK)
    {{ X=m /\ 0*0 <= m }}
      Z := 0
                 {{ X=m /\ Z*Z <= m }};
      while (Z+1)*(Z+1) <= X do
                 {{ X=m /\ Z*Z<=m /\ (Z+1)*(Z+1)<=X }} ->>  (c - OK)
                 {{ X=m /\ (Z+1)*(Z+1)<=m }}
        Z := Z + 1
                 {{ X=m /\ Z*Z<=m }}
      end
    {{ X=m /\ Z*Z<=m /\ ~((Z+1)*(Z+1)<=X) }} ->>            (b - OK)
    {{ Z*Z<=m /\ m<(Z+1)*(Z+1) }}

    This works, since conditions (a), (b), and (c) are now all
    trivially satisfied.

    Very often, when a variable is used in a loop in a read-only
    fashion (i.e., it is referred to by the program or by the
    specification and it is not changed by the loop), it is necessary
    to record the fact that it doesn't change in the loop invariant. *)

(** **** Exercise: 3 stars, standard, optional (sqrt)

    Translate the above informal decorated program into a formal one
    and prove it correct.

    Hint: The loop invariant here must ensure that Z*Z is consistently
    less than or equal to X. *)

Definition ex_sqrt (m:nat) :=
  <{
      Z := 0;
      while ((Z+1)*(Z+1) <= X) do
        Z := Z + 1
      end
  }>.

Theorem sqrt_correct : forall (m: nat),
    {{ X = m }}
      ex_sqrt m
    {{ Z*Z<=m /\ m<(Z+1)*(Z+1) }}.
Proof. (* FILL IN HERE *) Admitted.

(* ================================================================= *)
(** ** Example: Squaring *)

(** Here is a program that squares [X] by repeated addition:

  {{ X = m }}
    Y := 0;
    Z := 0;
    while Y <> X  do
      Z := Z + X;
      Y := Y + 1
    end
  {{ Z = m*m }}
*)

(** The first thing to note is that the loop reads [X] but doesn't
    change its value. As we saw in the previous example, it can be a good idea
    in such cases to add [X = m] to the loop invariant.  The other thing
    that we know is often useful in the loop invariant is the postcondition,
    so let's add that too, leading to the candidate loop invariant
    [Z = m * m /\ X = m].

    {{ X = m }} ->>                                       (a - WRONG)
    {{ 0 = m*m /\ X = m }}
      Y := 0
                   {{ 0 = m*m /\ X = m }};
      Z := 0
                   {{ Z = m*m /\ X = m }};
      while Y <> X do
                   {{ Z = m*m /\ X = m /\ Y <> X }} ->>   (c - WRONG)
                   {{ Z+X = m*m /\ X = m }}
        Z := Z + X
                   {{ Z = m*m /\ X = m }};
        Y := Y + 1
                   {{ Z = m*m /\ X = m }}
      end
    {{ Z = m*m /\ X = m /\ ~(Y <> X) }} ->>               (b - OK)
    {{ Z = m*m }}

    Conditions (a) and (c) fail because of the [Z = m*m] part.  While
    [Z] starts at [0] and works itself up to [m*m], we can't expect
    [Z] to be [m*m] from the start.  If we look at how [Z] progresses
    in the loop, after the 1st iteration [Z = m], after the 2nd
    iteration [Z = 2*m], and at the end [Z = m*m].  Since the variable
    [Y] tracks how many times we go through the loop, this leads us to
    derive a new loop invariant candidate: [Z = Y*m /\ X = m].

    {{ X = m }} ->>                                        (a - OK)
    {{ 0 = 0*m /\ X = m }}
      Y := 0
                    {{ 0 = Y*m /\ X = m }};
      Z := 0
                    {{ Z = Y*m /\ X = m }};
      while Y <> X do
                    {{ Z = Y*m /\ X = m /\ Y <> X }} ->>   (c - OK)
                    {{ Z+X = (Y+1)*m /\ X = m }}
        Z := Z + X
                    {{ Z = (Y+1)*m /\ X = m }};
        Y := Y + 1
                    {{ Z = Y*m /\ X = m }}
      end
    {{ Z = Y*m /\ X = m /\ ~(Y <> X) }} ->>                (b - OK)
    {{ Z = m*m }}

    This new loop invariant makes the proof go through: all three
    conditions are easy to check.

    It is worth comparing the postcondition [Z = m*m] and the [Z =
    Y*m] conjunct of the loop invariant. It is often the case that one has
    to replace parameters with variables -- or with expressions
    involving both variables and parameters, like [m - Y] -- when
    going from postconditions to loop invariants. *)

(** [] *)

(* ================================================================= *)
(** ** Exercise: Factorial *)

(** **** Exercise: 4 stars, advanced (factorial_correct)

    Recall that [n!] denotes the factorial of [n] (i.e., [n! =
    1*2*...*n]).  Formally, the factorial function is defined
    recursively in the Coq standard library in a way that is
    equivalent to the following:

    Fixpoint fact (n : nat) : nat :=
      match n with
      | O => 1
      | S n' => n * (fact n')
      end.
*)

Compute fact 5. (* ==> 120 *)

(** First, write the Imp program [factorial] that calculates the factorial
    of the number initially stored in the variable [X] and puts it in
    the variable [Y].
*)

(** Using your definition [factorial] and [slow_assignment_dec] as a
    guide, write a formal decorated program [factorial_dec] that
    implements the factorial function.  Hint: recall the use of [ap]
    in assertions to apply a function to an Imp variable.

    Fill in the blanks and finish the proof of correctness. Bear in mind
    that we are working with natural numbers, for which both division
    and subtraction can behave differently than with real numbers.
    Excluding both operations from your loop invariant is advisable!

    Then state a theorem named [factorial_correct] that says
    [factorial_dec] is correct, and prove the theorem.  If all goes
    well, [verify] will leave you with just two subgoals, each of
    which requires establishing some mathematical property of [fact],
    rather than proving anything about your program.

    Hint: if those two subgoals become tedious to prove, give some
    thought to how you could restate your assertions such that the
    mathematical operations are more amenable to manipulation in Coq.
    For example, recall that [1 + ...] is easier to work with than
    [... + 1]. *)

Example ex_factorial : com
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Definition factorial_pre (m:nat) : Assertion := FILL_IN_HERE.

Definition factorial_post (m:nat) : Assertion := FILL_IN_HERE.

(* FILL IN HERE *)

Theorem factorial_correct: forall (m: nat),
    {{ $(factorial_pre m) }} ex_factorial {{ $(factorial_post m) }}.
Proof. (* FILL IN HERE *) Admitted.
(** [] *)
