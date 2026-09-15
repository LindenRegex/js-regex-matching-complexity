From Linden Require Export Regex Parameters.
From Linden Require Import Chars.
From Warblre Require Import Base.
From Stdlib Require Import Lia.
From JsRegexOptp Require Export LindenExtensions.

Section Basics.
  Context {params: LindenParameters}.

  Fixpoint expanded_size (r: regex): nat := match r with
  | Epsilon | Regex.Character _ => 1
  | Disjunction r1 r2 | Sequence r1 r2 => 1 + expanded_size r1 + expanded_size r2
  | Quantified _ min _ r1 => (S min) * (3 + expanded_size r1)
  | Lookaround _ r1 => 1 + expanded_size r1
  | Group _ r1 => 2 + expanded_size r1 (* Open, Close *)
  | Anchor _ | Backreference _ => 1
  end.

  Fixpoint regex_size (r: regex): nat :=
    match r with
    | Epsilon | Regex.Character _ | Anchor _ | Backreference _ => 1
    | Disjunction r1 r2 | Sequence r1 r2 => 1 + regex_size r1 + regex_size r2
    | Quantified _ _ _ r1 | Lookaround _ r1 | Group _ r1 => 1 + regex_size r1
    end.

  Definition fuel_budget (r: regex) (inp: input): nat :=
    S ((1 + length (input_str inp))
       * (expanded_size r + expanded_size r * expanded_size r)).

  Definition guess_budget (r: regex) (inp: input): nat :=
    S (3 * ((1 + remaining_length inp forward) * regex_size r)).

  Definition expanded_budget (r: regex) (inp: input): nat :=
    S ((1 + remaining_length inp forward) * expanded_size r).

  Fixpoint no_lookaround (r: regex): Prop :=
    match r with
    | Epsilon | Regex.Character _ | Anchor _ | Backreference _ => True
    | Disjunction r1 r2 | Sequence r1 r2 => no_lookaround r1 /\ no_lookaround r2
    | Quantified _ _ _ r1 | Group _ r1 => no_lookaround r1
    | Lookaround _ _ => False
    end.

  Lemma size_le_expanded r: regex_size r <= expanded_size r.
  Proof. induction r; cbn; nia. Qed.

  Lemma expanded_size_pos r: 1 <= expanded_size r.
  Proof. induction r; cbn; nia. Qed.

  Fixpoint no_neg_lookaround (r: regex): Prop :=
    match r with
    | Epsilon | Regex.Character _ | Anchor _ | Backreference _ => True
    | Disjunction r1 r2 | Sequence r1 r2 => no_neg_lookaround r1 /\ no_neg_lookaround r2
    | Quantified _ _ _ r1 | Group _ r1 => no_neg_lookaround r1
    | Lookaround lk r1 => positivity lk = true /\ no_neg_lookaround r1
    end.

  Fixpoint no_lower_bound (r: regex): Prop :=
    match r with
    | Epsilon | Regex.Character _ | Anchor _ | Backreference _ => True
    | Disjunction r1 r2 | Sequence r1 r2 => no_lower_bound r1 /\ no_lower_bound r2
    | Quantified _ min _ r1 => min = 0 /\ no_lower_bound r1
    | Lookaround _ r1 | Group _ r1 => no_lower_bound r1
    end.

  Lemma expanded_size_nolb r: no_lower_bound r -> expanded_size r <= 3 * regex_size r.
  Proof. induction r; cbn; intuition (subst; lia). Qed.

  Lemma expanded_budget_le_guess_budget r inp:
      no_lower_bound r -> expanded_budget r inp <= guess_budget r inp.
  Proof.
    intro NLB; unfold expanded_budget, guess_budget.
    pose proof expanded_size_nolb r NLB; nia.
  Qed.
End Basics.
