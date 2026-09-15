From Linden Require Import Chars Groups.
From JsRegexOptp Require Import Qbf Basics RegexEncoding.
From Warblre Require Import Base.
From Stdlib Require Import List Lia.
Import ListNotations.

Section RegexEncodingPoslk.
  Context {params: LindenParameters}.
  Context (a_char semicolon_char z_char: Parameters.Character).
  Context (q: qbf).

  Let quants := fst q.
  Let n := length quants.
  Let form := snd q.
  Let pos_form := inner_pos_formula form.

  Let a_char_r := Regex.Character (CdSingle a_char).
  Let semicolon_char_r := Regex.Character (CdSingle semicolon_char).
  Let z_char_r := Regex.Character (CdSingle z_char).

  Definition a_semicolon_star := Quantified true 0 +∞ (Sequence a_char_r semicolon_char_r).

  Definition capture_z_regex (gid: group_id): regex :=
    Sequence
      a_semicolon_star
      (Group gid z_char_r).

  Definition check_z_regex (gid: group_id): regex :=
    Sequence
      (Sequence a_semicolon_star (Backreference gid))
      (Anchor EndInput).

  Fixpoint num_notexists (ql: list quantifier): nat :=
    match ql with
    | [] => 0
    | Qbf.Exists :: ql => num_notexists ql
    | Qbf.NotExists :: ql => S (num_notexists ql)
    end.

  Definition negation_regex (rsub: regex) (z_gid: group_id): regex :=
    Sequence
      (Lookaround LookAhead
          (Disjunction rsub (capture_z_regex z_gid)))
        (check_z_regex z_gid).

  Definition check_formula_regex: regex :=
    let conj_regex := check_conjunct_regex a_char semicolon_char (rev pos_form) in
    match form with
    | PosForm _ => conj_regex
    | NegForm _ => negation_regex conj_regex (S n)
    end.

  (* ql is the list of quantifiers including the current NotExists *)
  Definition z_gid_at (ql: list quantifier): nat :=
    match form with
    | PosForm _ => n + num_notexists ql
    | NegForm _ => n + S (num_notexists ql)
    end.
    
  Fixpoint theRegex_aux (v: variable) (ql: list quantifier) {struct ql}: regex :=
    match ql with
    | nil => check_formula_regex
    | Qbf.Exists::ql => Sequence (def_var_regex a_char semicolon_char v) (theRegex_aux (S v) ql)
    | Qbf.NotExists::ql' =>
      let z_gid := z_gid_at ql in
      let rsub := Sequence (def_var_regex a_char semicolon_char v) (theRegex_aux (S v) ql') in
      negation_regex rsub z_gid
    end.
  
  Definition theRegex := theRegex_aux 1 (fst q).

  (* The string: same as "normal" regex encoding *)
  (* Definition theString: LWParameters.string :=
    List.concat (List.repeat [a_char; semicolon_char] (List.length (fst q) + List.length (snd q))) ++ [z_char]. *)

End RegexEncodingPoslk.

Section Fragment.
  Context {params: LindenParameters}.
  Context (a_char semicolon_char z_char: Parameters.Character).

  Local Ltac frag_cbn :=
    unfold frag_regex in *;
    cbn [no_lower_bound no_neg_lookaround positivity def_var_regex check_literal_regex
         check_clause_regex_aux check_clause_regex check_conjunct_regex
         a_semicolon_star capture_z_regex check_z_regex negation_regex
         check_formula_regex theRegex_aux] in *.

  Lemma negation_regex_frag:
    forall rsub z_gid, frag_regex rsub ->
      frag_regex (negation_regex a_char semicolon_char z_char rsub z_gid).
  Proof. intros rsub z_gid F; frag_cbn; intuition auto. Qed.

  Lemma poslk_check_formula_regex_frag:
    forall q, frag_regex (check_formula_regex a_char semicolon_char z_char q).
  Proof.
    intro q; unfold check_formula_regex;
      pose proof check_conjunct_regex_frag a_char semicolon_char (rev (inner_pos_formula (snd q)));
      destruct (snd q); auto using negation_regex_frag.
  Qed.

  Lemma poslk_theRegex_aux_frag:
    forall q ql v, frag_regex (theRegex_aux a_char semicolon_char z_char q v ql).
  Proof.
    intros q ql; induction ql as [|[] ql IH]; intro v;
      [pose proof poslk_check_formula_regex_frag q | (pose proof (IH (S v))) ..];
      frag_cbn; auto using negation_regex_frag; intuition auto.
  Qed.

  Theorem theRegex_poslk_nolb:
    forall q, no_lower_bound (theRegex a_char semicolon_char z_char q).
  Proof. intro q; apply poslk_theRegex_aux_frag. Qed.

  Theorem theRegex_poslk_noneglk:
    forall q, no_neg_lookaround (theRegex a_char semicolon_char z_char q).
  Proof. intro q; apply poslk_theRegex_aux_frag. Qed.
End Fragment.

Section Size.
  Context {params: LindenParameters}.
  Context (a_char semicolon_char z_char: Parameters.Character).

  Local Ltac size_cbn_poslk :=
    cbn [expanded_size num_literals_pos_formula length repeat
         def_var_regex check_literal_regex check_clause_regex_aux
         check_clause_regex check_conjunct_regex
         RegexEncoding.theRegex_aux theRegex_aux
         negation_regex capture_z_regex check_z_regex a_semicolon_star] in *.

  Section PosLookaheadEncoding.
    Context (q: qbf).

    Lemma poslk_check_formula_regex_size:
      expanded_size (check_formula_regex a_char semicolon_char z_char q) <=
        24 + 4 * num_clauses_qbf q + 4 * num_literals_qbf q.
    Proof.
      unfold check_formula_regex; measure_unfold;
        destruct (snd q) as [pf|pf]; pose proof check_conjunct_regex_rev_size a_char semicolon_char pf; size_cbn_poslk; lia.
    Qed.

    Lemma poslk_theRegex_aux_size:
      forall ql v,
        expanded_size (theRegex_aux a_char semicolon_char z_char q v ql) <=
          31 * length ql + 24 + 4 * num_clauses_qbf q + 4 * num_literals_qbf q.
    Proof.
      intro ql; induction ql as [|[] ql IH]; intro v;
        [pose proof poslk_check_formula_regex_size | (pose proof (IH (S v))) ..]; size_cbn_poslk; lia.
    Qed.

    Theorem theRegex_poslk_size_parts:
      expanded_size (theRegex a_char semicolon_char z_char q) <=
        31 * length (fst q) + 4 * num_clauses_qbf q + 4 * num_literals_qbf q + 24.
    Proof. unfold theRegex; pose proof poslk_theRegex_aux_size (fst q) 1; lia. Qed.

    Theorem theRegex_poslk_size:
      expanded_size (theRegex a_char semicolon_char z_char q) <=
        31 * qbf_size q.
    Proof. unfold qbf_size; pose proof theRegex_poslk_size_parts; lia. Qed.
  End PosLookaheadEncoding.

  Lemma num_literals_pos_formula_repeat:
    forall c m, num_literals_pos_formula (repeat c m) = m * length c.
  Proof. intros c m; induction m; cbn; lia. Qed.

  Lemma check_conjunct_negvar_size:
    forall m, expanded_size (check_conjunct_regex a_char semicolon_char (repeat [NegVar 1] m)) =
      1 + 8 * m.
  Proof. intro m; induction m; size_cbn_poslk; lia. Qed.

  Lemma theRegex_aux_worst_case:
    forall q m, snd q = NegForm (repeat [NegVar 1] m) ->
      forall k v,
        expanded_size (RegexEncoding.theRegex_aux q a_char semicolon_char v (repeat NotExists k)) =
          9 * k + 8 * m + 2.
  Proof.
    intros ? m Hq k; induction k as [|k IH]; intro v; size_cbn_poslk;
      [rewrite Hq; cbn [RegexEncoding.check_formula_regex]; rewrite rev_repeat;
       pose proof check_conjunct_negvar_size m
      |pose proof (IH (S v))]; size_cbn_poslk; lia.
  Qed.

  Lemma poslk_theRegex_aux_worst_case:
    forall q m, snd q = NegForm (repeat [NegVar 1] m) ->
      forall k v,
        expanded_size
          (theRegex_aux a_char semicolon_char z_char q v (repeat NotExists k)) =
          31 * k + 8 * m + 24.
  Proof.
    intros ? m Hq k; induction k as [|k IH]; intro v; size_cbn_poslk;
      [unfold check_formula_regex; rewrite Hq;
       cbn [inner_pos_formula]; rewrite rev_repeat; pose proof check_conjunct_negvar_size m
      |pose proof (IH (S v))]; size_cbn_poslk; lia.
  Qed.

  Theorem reduction_size_tight:
    forall n m,
      qbf_size (repeat NotExists n, NegForm (repeat [NegVar 1] m)) = 1 + n + 2 * m /\
      expanded_size (RegexEncoding.theRegex (repeat NotExists n, NegForm (repeat [NegVar 1] m))
                    a_char semicolon_char) = 9 * n + 8 * m + 2 /\
      expanded_size (theRegex a_char semicolon_char z_char
                    (repeat NotExists n, NegForm (repeat [NegVar 1] m))) = 31 * n + 8 * m + 24.
  Proof.
    intros; unfold qbf_size, RegexEncoding.theRegex, theRegex;
      measure_unfold; cbn [fst snd inner_pos_formula];
      rewrite !repeat_length, num_literals_pos_formula_repeat; repeat split;
      eauto using theRegex_aux_worst_case, poslk_theRegex_aux_worst_case; size_cbn_poslk; lia.
  Qed.

End Size.
