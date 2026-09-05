From Linden Require Import Chars.
From JsRegexOptp Require Import Qbf Basics.
From Stdlib Require Import List.
Import ListNotations.

Section RegexEncoding.
  Context {params: LindenParameters}.
  Context (q: qbf).

  Context (x_char semicolon_char n_char: Parameters.Character).

  (* Regex used to define a variable: <(_i x)|x>; *)
  Definition def_var_regex (v: variable): regex :=
    Sequence
      (Disjunction
        (Group v (Character (CdSingle x_char)))
        (Character (CdSingle x_char)))
      (Character (CdSingle semicolon_char)).

  Definition check_literal_regex (l: literal): regex :=
    match l with
    | PosVar v => Backreference v
    | NegVar v => Sequence (Backreference v) (Character (CdSingle x_char))
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
    List.concat (List.repeat [x_char; semicolon_char] (List.length (fst q) + num_clauses_qbf q)) ++ [n_char].

End RegexEncoding.

Section Fragment.
  Context {params: LindenParameters}.
  Context (x_char semicolon_char: Parameters.Character).

  Definition frag_regex (r: regex): Prop := no_lower_bound r /\ no_neg_lookaround r.

  Local Ltac frag_cbn :=
    unfold frag_regex in *;
    cbn [no_lower_bound no_neg_lookaround def_var_regex check_literal_regex
         check_clause_regex_aux check_clause_regex check_conjunct_regex
         check_formula_regex theRegex_aux] in *.

  Lemma check_clause_regex_frag:
    forall c, frag_regex (check_clause_regex x_char semicolon_char c).
  Proof.
    intro c; enough (frag_regex (check_clause_regex_aux x_char c)) by (frag_cbn; tauto);
      induction c as [|[] c IH]; frag_cbn; tauto.
  Qed.

  Lemma check_conjunct_regex_frag:
    forall cl, frag_regex (check_conjunct_regex x_char semicolon_char cl).
  Proof.
    induction cl as [|c cl IH]; [|pose proof check_clause_regex_frag c]; frag_cbn; tauto.
  Qed.

  Lemma check_formula_regex_nolb:
    forall f, no_lower_bound (check_formula_regex x_char semicolon_char f).
  Proof. intros [pf|pf]; pose proof check_conjunct_regex_frag (rev pf); frag_cbn; tauto. Qed.

  Lemma theRegex_aux_nolb:
    forall q ql v, no_lower_bound (theRegex_aux q x_char semicolon_char v ql).
  Proof.
    intros q ql; induction ql as [|[] ql IH]; intro v;
      [pose proof check_formula_regex_nolb (snd q) | (pose proof (IH (S v))) ..];
      frag_cbn; tauto.
  Qed.

  Theorem theRegex_nolb:
    forall q, no_lower_bound (theRegex q x_char semicolon_char).
  Proof. intro q; apply theRegex_aux_nolb. Qed.
End Fragment.
