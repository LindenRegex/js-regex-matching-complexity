From Linden Require Import Regex Chars Parameters Groups.
From JsRegexOptp Require Import Qbf RegexEncoding.
From Warblre Require Import Base.
Require Import List.
Import ListNotations.

Section RegexEncodingPoslk.
  Context {params: LindenParameters}.
  Context (x_char semicolon_char n_char: Parameters.Character).
  Context (q: qbf).

  Let quants := fst q.
  Let n := length quants.

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
    
  Fixpoint theRegex_aux (v: variable) (ql: list quantifier) {struct ql}: regex :=
    match ql with
    | nil => check_conjunct_regex x_char semicolon_char (rev (snd q))
    | Qbf.Exists::ql => Sequence (def_var_regex x_char semicolon_char v) (theRegex_aux (S v) ql)
    | Qbf.NotExists::ql =>
      let n_gid := n + S (num_notexists ql) in
      Sequence
        (Lookaround LookAhead
          (Disjunction
            (Sequence (def_var_regex x_char semicolon_char v) (theRegex_aux (S v) ql))
            (capture_n_regex n_gid)))
        (check_n_regex n_gid)
    end.
  
  Definition theRegex := theRegex_aux 1 (fst q).

  (* The string *)
  Definition theString: LWParameters.string :=
    List.concat (List.repeat [x_char; semicolon_char] (List.length (fst q) + List.length (snd q))) ++ [n_char].

End RegexEncodingPoslk.