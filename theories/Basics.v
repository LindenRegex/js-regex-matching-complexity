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

End Basics.
