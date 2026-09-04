(* TODO: Upstream in Warblre. *)

From Warblre Require Import Patterns Numeric Node NodeProps StaticSemantics Result
  Base EarlyErrors Parameters RegExpRecord Semantics Frontend Notation Errors Typeclasses Match.
From Stdlib Require Import List Lia PeanoNat ZArith.
Import ListNotations.

Section WarblreEarlyErrors.
  Context {params: Parameters}.

  Definition simple_quantifier (q: Patterns.Quantifier): Prop :=
    match q with
    | Patterns.Greedy p | Patterns.Lazy p =>
        match p with Patterns.RepRange lo hi => lo <= hi | _ => True end
    end.

  Fixpoint simple_regex (n: nat) (r: Patterns.Regex): Prop :=
    match r with
    | Patterns.Empty | Patterns.Char _ | Patterns.Dot
    | Patterns.InputStart | Patterns.InputEnd
    | Patterns.WordBoundary | Patterns.NotWordBoundary => True
    | Patterns.AtomEsc (Patterns.DecimalEsc k) => positive_to_nat k <= n
    | Patterns.AtomEsc (Patterns.GroupEsc _) => False
    | Patterns.AtomEsc _ => True
    | Patterns.CharacterClass _ => False
    | Patterns.Disjunction r1 r2 | Patterns.Seq r1 r2 =>
        simple_regex n r1 /\ simple_regex n r2
    | Patterns.Quantified r1 q => simple_regex n r1 /\ simple_quantifier q
    | Patterns.Group None r1 => simple_regex n r1
    | Patterns.Group (Some _) _ => False
    | Patterns.Lookahead r1 | Patterns.NegativeLookahead r1
    | Patterns.Lookbehind r1 | Patterns.NegativeLookbehind r1 => simple_regex n r1
    end.

  Lemma simple_Pass_Quantifier q: simple_quantifier q -> EarlyErrors.Pass_Quantifier q.
  Proof. destruct q as [[]|[]]; constructor; now constructor. Qed.

  Local Ltac peel_simple :=
    repeat match goal with
           | [ H: simple_regex _ _ |- _ ] => progress cbn [simple_regex] in H
           | [ H: simple_quantifier _ |- _ ] => apply simple_Pass_Quantifier in H
           | [ H: List.In _ nil |- _ ] => destruct H
           | [ H: List.In _ (_ ++ _) |- _ ] => apply in_app_or in H as []
           | [ H: _ /\ _ |- _ ] => destruct H
           | [ H: False |- _ ] => destruct H
           | [ x: option Patterns.GroupName |- _ ] => destruct x
           | [ x: Patterns.AtomEscape |- _ ] => destruct x
           end.

  Lemma simple_regex_walk r:
    forall n ctx nd,
      simple_regex n r ->
      List.In nd (Zipper.Walk.walk r ctx) ->
      simple_regex n (fst nd).
  Proof.
    induction r; intros n ctx nd SIMPLE [<- | IN]; try exact SIMPLE; peel_simple; eauto.
  Qed.

  Lemma simple_Pass_Regex r:
    forall ctx,
      simple_regex (StaticSemantics.countLeftCapturingParensWithin (Node.zip r ctx) nil) r ->
      EarlyErrors.Pass_Regex r ctx.
  Proof.
    induction r; intros ctx SIMPLE; peel_simple; constructor; auto; now constructor.
  Qed.

  Theorem simple_earlyErrors r:
      simple_regex (StaticSemantics.countLeftCapturingParensWithin r nil) r ->
      StaticSemantics.earlyErrors r nil = Success false.
  Proof.
    intro SIMPLE; unfold StaticSemantics.earlyErrors.
    erewrite EarlyErrors.exist_all_false; [now apply EarlyErrors.soundness_rec, simple_Pass_Regex|].
    intros [r0 ctx0] IN0; apply EarlyErrors.exist_all_false; intros [] _.
    destruct (_ =?= _)%wt, r0; try destruct name; try reflexivity.
    destruct (simple_regex_walk _ _ _ _ SIMPLE IN0).
  Qed.

End WarblreEarlyErrors.
