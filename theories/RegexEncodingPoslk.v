From Linden Require Import Regex Chars Parameters Groups.
From JsRegexOptp Require Import Qbf RegexEncoding.
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