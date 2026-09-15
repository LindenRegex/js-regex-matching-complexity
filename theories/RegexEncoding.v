From Linden Require Import Chars.
From JsRegexOptp Require Import Qbf Basics.
From Stdlib Require Import List Lia.
Import ListNotations.

Section RegexEncoding.
  Context {params: LindenParameters}.
  Context (q: qbf).

  Context (a_char semicolon_char z_char: Parameters.Character).

  (* Regex used to define a variable: <(_i x)|x>; *)
  Definition def_var_regex (v: variable): regex :=
    Sequence
      (Disjunction
        (Group v (Character (CdSingle a_char)))
        (Character (CdSingle a_char)))
      (Character (CdSingle semicolon_char)).

  Definition check_literal_regex (l: literal): regex :=
    match l with
    | PosVar v => Backreference v
    | NegVar v => Sequence (Backreference v) (Character (CdSingle a_char))
    end.
  
  Fixpoint check_clause_regex_aux (c: clause): regex :=
    match c with
    | nil => Epsilon
    | l::q => Disjunction (check_literal_regex l) (check_clause_regex_aux q)
    end.

  Definition check_clause_regex (c: clause): regex :=
    Sequence (check_clause_regex_aux c) (Character (CdSingle semicolon_char)).

  Fixpoint check_conjunct_regex (rev_cl: list clause): regex :=
    match rev_cl with
    | nil => Epsilon
    | c::cl => Sequence (check_conjunct_regex cl) (check_clause_regex c)
    end.

  Definition check_formula_regex (f: formula): regex :=
    match f with
    | PosForm pf => check_conjunct_regex (rev pf)
    | NegForm pf => Lookaround NegLookAhead (check_conjunct_regex (rev pf))
    end.

  (* The regex *)
  Fixpoint theRegex_aux (v: variable) (ql: list quantifier) {struct ql}: regex :=
    match ql with
    | nil => check_formula_regex (snd q)
    | Qbf.Exists::ql => Sequence (def_var_regex v) (theRegex_aux (S v) ql)
    | Qbf.NotExists::ql => Lookaround NegLookAhead (Sequence (def_var_regex v) (theRegex_aux (S v) ql))
    end.
  
  Definition theRegex := theRegex_aux 1 (fst q).

  (* The string *)
  Definition theString: LWParameters.string :=
    List.concat (List.repeat [a_char; semicolon_char] (List.length (fst q) + num_clauses_qbf q)) ++ [z_char].

End RegexEncoding.

Section Fragment.
  Context {params: LindenParameters}.
  Context (a_char semicolon_char: Parameters.Character).

  Definition frag_regex (r: regex): Prop := no_lower_bound r /\ no_neg_lookaround r.

  Local Ltac frag_cbn :=
    unfold frag_regex in *;
    cbn [no_lower_bound no_neg_lookaround def_var_regex check_literal_regex
         check_clause_regex_aux check_clause_regex check_conjunct_regex
         check_formula_regex theRegex_aux] in *.

  Lemma check_clause_regex_frag:
    forall c, frag_regex (check_clause_regex a_char semicolon_char c).
  Proof.
    intro c; enough (frag_regex (check_clause_regex_aux a_char c)) by (frag_cbn; tauto);
      induction c as [|[] c IH]; frag_cbn; tauto.
  Qed.

  Lemma check_conjunct_regex_frag:
    forall cl, frag_regex (check_conjunct_regex a_char semicolon_char cl).
  Proof.
    induction cl as [|c cl IH]; [|pose proof check_clause_regex_frag c]; frag_cbn; tauto.
  Qed.

  Lemma check_formula_regex_nolb:
    forall f, no_lower_bound (check_formula_regex a_char semicolon_char f).
  Proof. intros [pf|pf]; pose proof check_conjunct_regex_frag (rev pf); frag_cbn; tauto. Qed.

  Lemma theRegex_aux_nolb:
    forall q ql v, no_lower_bound (theRegex_aux q a_char semicolon_char v ql).
  Proof.
    intros q ql; induction ql as [|[] ql IH]; intro v;
      [pose proof check_formula_regex_nolb (snd q) | (pose proof (IH (S v))) ..];
      frag_cbn; tauto.
  Qed.

  Theorem theRegex_nolb:
    forall q, no_lower_bound (theRegex q a_char semicolon_char).
  Proof. intro q; apply theRegex_aux_nolb. Qed.
End Fragment.

Lemma num_literals_pos_formula_app:
  forall pf1 pf2, num_literals_pos_formula (pf1 ++ pf2) =
    num_literals_pos_formula pf1 + num_literals_pos_formula pf2.
Proof. intros pf1 pf2; induction pf1; cbn; lia. Qed.

Lemma num_literals_pos_formula_rev:
  forall pf, num_literals_pos_formula (rev pf) = num_literals_pos_formula pf.
Proof. intro pf; induction pf; cbn; rewrite ?num_literals_pos_formula_app; cbn; lia. Qed.

Ltac size_cbn :=
  cbn [expanded_size num_literals_pos_formula length repeat
       def_var_regex check_literal_regex check_clause_regex_aux
       check_clause_regex check_conjunct_regex
       theRegex_aux] in *.

Ltac measure_unfold :=
  unfold num_clauses_qbf, num_literals_qbf, num_clauses_formula,
    num_literals_formula, inner_pos_formula.

Section Size.
  Context {params: LindenParameters}.
  Context (a_char semicolon_char: Parameters.Character).

  Lemma check_literal_regex_size:
    forall l, expanded_size (check_literal_regex a_char l) <= 3.
  Proof. destruct l; size_cbn; lia. Qed.

  Lemma check_clause_regex_aux_size:
    forall c, expanded_size (check_clause_regex_aux a_char c) <= 1 + 4 * length c.
  Proof. induction c as [|l c IH]; [|pose proof check_literal_regex_size l]; size_cbn; lia. Qed.

  Lemma check_clause_regex_size:
    forall c, expanded_size (check_clause_regex a_char semicolon_char c) <= 3 + 4 * length c.
  Proof. intro c; pose proof check_clause_regex_aux_size c; size_cbn; lia. Qed.

  Lemma check_conjunct_regex_size:
    forall cl, expanded_size (check_conjunct_regex a_char semicolon_char cl) <=
      1 + 4 * length cl + 4 * num_literals_pos_formula cl.
  Proof. induction cl as [|c cl IH]; [|pose proof check_clause_regex_size c]; size_cbn; lia. Qed.

  Lemma check_conjunct_regex_rev_size:
    forall pf, expanded_size (check_conjunct_regex a_char semicolon_char (rev pf)) <=
      1 + 4 * length pf + 4 * num_literals_pos_formula pf.
  Proof.
    intro pf; pose proof check_conjunct_regex_size (rev pf) as H;
      rewrite length_rev, num_literals_pos_formula_rev in H; lia.
  Qed.

  Section NegLookaheadEncoding.
    Context (q: qbf).

    (* Negation costs one extra node (for the negative lookahead). *)
    Lemma check_formula_regex_size:
      expanded_size (RegexEncoding.check_formula_regex a_char semicolon_char (snd q)) <=
        2 + 4 * num_clauses_qbf q + 4 * num_literals_qbf q.
    Proof.
      measure_unfold; destruct (snd q) as [pf|pf]; pose proof check_conjunct_regex_rev_size pf;
        cbn [RegexEncoding.check_formula_regex]; size_cbn; lia.
    Qed.

    Lemma theRegex_aux_size:
      forall ql v, expanded_size (RegexEncoding.theRegex_aux q a_char semicolon_char v ql) <=
        9 * length ql + 2 + 4 * num_clauses_qbf q + 4 * num_literals_qbf q.
    Proof.
      intro ql; induction ql as [|[] ql IH]; intro v;
        [pose proof check_formula_regex_size | (pose proof (IH (S v))) ..]; size_cbn; lia.
    Qed.

    Theorem theRegex_size_parts:
      expanded_size (RegexEncoding.theRegex q a_char semicolon_char) <=
        9 * length (fst q) + 4 * num_clauses_qbf q + 4 * num_literals_qbf q + 2.
    Proof. unfold RegexEncoding.theRegex; pose proof theRegex_aux_size (fst q) 1; lia. Qed.

    Theorem theRegex_size:
      expanded_size (RegexEncoding.theRegex q a_char semicolon_char) <= 9 * qbf_size q.
    Proof. unfold qbf_size; pose proof theRegex_size_parts; lia. Qed.
  End NegLookaheadEncoding.

End Size.
