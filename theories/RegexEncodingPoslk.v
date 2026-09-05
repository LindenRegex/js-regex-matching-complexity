From Linden Require Import Chars Groups.
From JsRegexOptp Require Import Qbf Basics RegexEncoding.
From Warblre Require Import Base.
From Stdlib Require Import List.
Import ListNotations.

Section RegexEncodingPoslk.
  Context {params: LindenParameters}.
  Context (x_char semicolon_char n_char: Parameters.Character).
  Context (q: qbf).

  Let quants := fst q.
  Let n := length quants.
  Let form := snd q.
  Let pos_form := inner_pos_formula form.

  Let x_char_r := Regex.Character (CdSingle x_char).
  Let semicolon_char_r := Regex.Character (CdSingle semicolon_char).
  Let n_char_r := Regex.Character (CdSingle n_char).

  Definition x_semicolon_star := Quantified true 0 +∞ (Sequence x_char_r semicolon_char_r).

  Definition capture_n_regex (gid: group_id): regex :=
    Sequence
      x_semicolon_star
      (Group gid n_char_r).

  Definition check_n_regex (gid: group_id): regex :=
    Sequence
      (Sequence x_semicolon_star (Backreference gid))
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
          (Disjunction rsub (capture_n_regex z_gid)))
        (check_n_regex z_gid).

  Definition check_formula_regex: regex :=
    let conj_regex := check_conjunct_regex x_char semicolon_char (rev pos_form) in
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
    | Qbf.Exists::ql => Sequence (def_var_regex x_char semicolon_char v) (theRegex_aux (S v) ql)
    | Qbf.NotExists::ql' =>
      let z_gid := z_gid_at ql in
      let rsub := Sequence (def_var_regex x_char semicolon_char v) (theRegex_aux (S v) ql') in
      negation_regex rsub z_gid
    end.
  
  Definition theRegex := theRegex_aux 1 (fst q).

  (* The string: same as "normal" regex encoding *)
  (* Definition theString: LWParameters.string :=
    List.concat (List.repeat [x_char; semicolon_char] (List.length (fst q) + List.length (snd q))) ++ [n_char]. *)

End RegexEncodingPoslk.

Section Fragment.
  Context {params: LindenParameters}.
  Context (x_char semicolon_char n_char: Parameters.Character).

  Local Ltac frag_cbn :=
    unfold frag_regex in *;
    cbn [no_lower_bound no_neg_lookaround positivity def_var_regex check_literal_regex
         check_clause_regex_aux check_clause_regex check_conjunct_regex
         x_semicolon_star capture_n_regex check_n_regex negation_regex
         check_formula_regex theRegex_aux] in *.

  Lemma negation_regex_frag:
    forall rsub z_gid, frag_regex rsub ->
      frag_regex (negation_regex x_char semicolon_char n_char rsub z_gid).
  Proof. intros rsub z_gid F; frag_cbn; intuition auto. Qed.

  Lemma poslk_check_formula_regex_frag:
    forall q, frag_regex (check_formula_regex x_char semicolon_char n_char q).
  Proof.
    intro q; unfold check_formula_regex;
      pose proof check_conjunct_regex_frag x_char semicolon_char (rev (inner_pos_formula (snd q)));
      destruct (snd q); auto using negation_regex_frag.
  Qed.

  Lemma poslk_theRegex_aux_frag:
    forall q ql v, frag_regex (theRegex_aux x_char semicolon_char n_char q v ql).
  Proof.
    intros q ql; induction ql as [|[] ql IH]; intro v;
      [pose proof poslk_check_formula_regex_frag q | (pose proof (IH (S v))) ..];
      frag_cbn; auto using negation_regex_frag; intuition auto.
  Qed.

  Theorem theRegex_poslk_nolb:
    forall q, no_lower_bound (theRegex x_char semicolon_char n_char q).
  Proof. intro q; apply (proj1 (poslk_theRegex_aux_frag q _ _)). Qed.

  Theorem theRegex_poslk_noneglk:
    forall q, no_neg_lookaround (theRegex x_char semicolon_char n_char q).
  Proof. intro q; apply (proj2 (poslk_theRegex_aux_frag q _ _)). Qed.
End Fragment.
