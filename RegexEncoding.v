From JsRegexOptp Require Import Qbf.
From Linden Require Import Regex Chars Parameters.
Require Import List.
Import ListNotations.

Section RegexEncoding.
  Context {params: LindenParameters}.
  Context (q: qbf).

  Context (x_char semicolon_char: Parameters.Character).

  (* Regex used to define a variable: <(_i x)|x>; *)
  Definition def_var_regex (v: variable): regex :=
    Sequence
      (Disjunction
        (Group v (Character (CdSingle x_char)))
        (Character (CdSingle x_char)))
      (Character (CdSingle semicolon_char)).

  (* Regex used to check a literal *)
  Definition check_literal_regex (l: literal): regex :=
    match l with
    | PosVar v => Backreference v
    | NegVar v => Sequence (Backreference v) (Character (CdSingle x_char))
    end.
  
  (* Regex used to check a clause *)
  Fixpoint check_clause_regex_aux (c: clause): regex :=
    match c with
    | nil => Epsilon
    | l::q => Disjunction (check_literal_regex l) (check_clause_regex_aux q)
    end.

  Definition check_clause_regex (c: clause): regex :=
    Sequence (check_clause_regex_aux c) (Character (CdSingle semicolon_char)).

  (* Regex used to check the conjunction *)
  Fixpoint check_conjunct_regex (cl: list clause): regex :=
    match cl with
    | nil => Epsilon
    | c::cl => Sequence (check_clause_regex c) (check_conjunct_regex cl)
    end.

  (* The regex *)
  Fixpoint theRegex_aux (v: variable) (ql: list quantifier) {struct ql}: regex :=
    match ql with
    | nil => check_conjunct_regex (snd q)
    | Qbf.Exists::ql => Sequence (def_var_regex v) (theRegex_aux (S v) ql)
    | Qbf.NotExists::ql => Lookaround NegLookAhead (Sequence (def_var_regex v) (theRegex_aux (S v) ql))
    end.
  
  Definition theRegex := theRegex_aux 1 (fst q).

  (* The string *)
  Definition theString: LWParameters.string :=
    List.concat (List.repeat [x_char; semicolon_char] (List.length (fst q) + List.length (snd q))).

End RegexEncoding.
