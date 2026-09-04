(** * The hardness results at a concrete ASCII engine, with no hypotheses left *)

From Stdlib Require Import List Ascii.
From JsRegexOptp Require Import Basics.
Import ListNotations.
From JsRegexOptp Require Import Qbf QbfPrenex RegexEncoding RegexEncodingPoslk
  HardnessProofs HardnessPoslk WarblreEncoding HardnessOptp MembershipOptp Bits GroupMaps
  MembershipProof LindenExtensions WarblreExtensions Warblre EndToEnd.
From Linden Require Import Inst LWParameters Chars Groups Semantics Tree RegexpTranslation
  FunctionalUtils ResultTranslation EquivMain.
From Warblre Require Import Parameters RegExpRecord Inst Patterns Semantics StaticSemantics Base
  Frontend Result Notation.

Definition ascii_char := @Parameters.Character.type (@char naive_params).

Definition x_char: ascii_char := $ "x"%char.
Definition semicolon_char: ascii_char := $ ";"%char.
Definition n_char: ascii_char := $ "n"%char.

Example x_char_value: x_char = 0x78 := eq_refl.
Example semicolon_char_value: semicolon_char = 0x3B := eq_refl.
Example n_char_value: n_char = 0x6E := eq_refl.

Definition ascii_regex (q: qbf): regex :=
  RegexEncoding.theRegex q x_char semicolon_char.

Definition ascii_regex_poslk (q: qbf): regex :=
  RegexEncodingPoslk.theRegex x_char semicolon_char n_char q.

Definition ascii_string (q: qbf): LWParameters.string :=
  RegexEncoding.theString q x_char semicolon_char n_char.

Definition rer_ascii (ngroups: nat): RegExpRecord :=
  RegExpRecord.make false false false tt ngroups.

Section AsciiInstantiation.
  Context (ngroups: nat).

  Let rer := rer_ascii ngroups.

  Lemma canonicalize_ascii_id (c: ascii_char): Character.canonicalize rer c = c.
  Proof. apply Character.canonicalize_casesenst; reflexivity. Qed.

  Lemma canonicalize_ascii_neq (c1 c2: ascii_char):
      c1 <> c2 -> Character.canonicalize rer c1 <> Character.canonicalize rer c2.
  Proof. rewrite !canonicalize_ascii_id; auto. Qed.

  Lemma x_semicolon_neq_ascii:
    Character.canonicalize rer x_char <>
    Character.canonicalize rer semicolon_char.
  Proof. apply canonicalize_ascii_neq; discriminate. Qed.

  Lemma x_n_neq_ascii:
    Character.canonicalize rer x_char <>
    Character.canonicalize rer n_char.
  Proof. apply canonicalize_ascii_neq; discriminate. Qed.

  Lemma x_not_lineterminator_ascii: ~ In x_char Character.line_terminators.
  Proof. simpl; intuition discriminate. Qed.

  Lemma n_not_lineterminator_ascii: ~ In n_char Character.line_terminators.
  Proof. simpl; intuition discriminate. Qed.

  Context (q: qbf).
  Hypothesis (WF_q: wf_qbf q).

  Corollary qbf_regex_ascii:
    regex_matches_string rer (ascii_regex q) (ascii_string q) <->
    qbf_true q = true.
  Proof. apply HardnessProofs.qbf_regex; auto using x_semicolon_neq_ascii. Qed.

  Corollary qbf_regex_poslk_ascii:
    regex_matches_string rer (ascii_regex_poslk q) (ascii_string q) <->
    qbf_true q = true.
  Proof.
    apply HardnessPoslk.qbf_regex; auto using x_semicolon_neq_ascii,
      x_n_neq_ascii, x_not_lineterminator_ascii, n_not_lineterminator_ascii.
  Qed.

End AsciiInstantiation.

Module Example.
  Definition q0: qbf := ([Qbf.Exists], PosForm [[PosVar 1]]).

  Lemma q0_wf: wf_qbf q0.
  Proof. repeat constructor; auto. Qed.

  Example q0_true: qbf_true q0 = true := eq_refl.
  Example q0_string: ascii_string q0 = [0x78; 0x3B; 0x78; 0x3B; 0x6E] := eq_refl.

  Example q0_matches (ngroups: nat):
    regex_matches_string
      (rer_ascii ngroups) (ascii_regex q0) (ascii_string q0) :=
    proj2 (qbf_regex_ascii ngroups q0 q0_wf) q0_true.
End Example.

Notation P := (@LWParameters.LWParameters naive_params) (only parsing).

#[local] Arguments Frontend.Null {C S UP}%_type_scope {H H0 H1} _.
#[local] Arguments Frontend.Exotic {C S UP}%_type_scope {H H0 H1} _ _.

Section AsciiEndToEnd.
  Notation flags_ascii := (reg_exp_flags false false false false false tt true) (only parsing).

  Notation rer_at wr := (rer_of wr flags_ascii) (only parsing).

  Example rer_at_value:
    forall wr: Patterns.Regex,
      @rer_of P wr flags_ascii
      = rer_ascii (StaticSemantics.countLeftCapturingParensWithin wr nil) := fun _ => eq_refl.

  Notation str pq := (ascii_string (qbf_of_pqbf pq)) (only parsing).

  Theorem pspace_hardness_matcher_ascii: forall pq: pqbf, wf_pqbf pq ->
    let wr := theRegex_w (qbf_of_pqbf pq) x_char semicolon_char in
    pattern_size wr <= 8 * pqbf_size pq /\
    length (str pq) <= 2 * pqbf_size pq /\
    @StaticSemantics.earlyErrors P wr [] = Success false /\
    no_lower_bound (linden_of wr) /\
    exists m res,
      @Semantics.compilePattern P wr (rer_at wr) = Success m /\
      m (str pq) 0 = Success res /\
      (res <> None <-> pqbf_true pq = true).
  Proof.
    intros pq WF; exact (pspace_hardness_matcher x_char semicolon_char n_char
                           false false false false pq WF (x_semicolon_neq_ascii _)).
  Qed.

  Theorem pspace_hardness_e2e_ascii: forall pq: pqbf, wf_pqbf pq ->
    let wr := theRegex_w (qbf_of_pqbf pq) x_char semicolon_char in
    pattern_size wr <= 8 * pqbf_size pq /\
    length (str pq) <= 2 * pqbf_size pq /\
    @StaticSemantics.earlyErrors P wr [] = Success false /\
    no_lower_bound (linden_of wr) /\
    exists inst res,
      @regExpInitialize P wr flags_ascii = Success inst /\
      RegExpInstance.regExpMatcher inst (str pq) 0 = Success res /\
      (res <> None <-> pqbf_true pq = true) /\
      ((exists inst', @regExpExec P inst (str pq) = Success (Null inst'))
       <-> pqbf_true pq = false) /\
      ((exists A inst', @regExpExec P inst (str pq) = Success (Exotic A inst'))
       <-> pqbf_true pq = true).
  Proof.
    intros pq WF; exact (pspace_hardness_e2e x_char semicolon_char n_char
                           false false false false pq WF (x_semicolon_neq_ascii _)).
  Qed.

  Theorem pspace_hardness_noneglk_matcher_ascii: forall pq: pqbf, wf_pqbf pq ->
    let wr := theRegex_poslk_w (qbf_of_pqbf pq) x_char semicolon_char n_char in
    pattern_size wr <= 25 * pqbf_size pq /\
    length (str pq) <= 2 * pqbf_size pq /\
    @StaticSemantics.earlyErrors P wr [] = Success false /\
    pattern_no_neg_lookaround wr /\
    no_lower_bound (linden_of wr) /\
    exists m res,
      @Semantics.compilePattern P wr (rer_at wr) = Success m /\
      m (str pq) 0 = Success res /\
      (res <> None <-> pqbf_true pq = true).
  Proof.
    intros pq WF; exact (pspace_hardness_noneglk_matcher x_char semicolon_char n_char
                           false false false false pq WF n_not_lineterminator_ascii
                           x_not_lineterminator_ascii
                           (x_semicolon_neq_ascii _) (x_n_neq_ascii _)).
  Qed.

  Theorem pspace_hardness_noneglk_e2e_ascii: forall pq: pqbf, wf_pqbf pq ->
    let wr := theRegex_poslk_w (qbf_of_pqbf pq) x_char semicolon_char n_char in
    pattern_size wr <= 25 * pqbf_size pq /\
    length (str pq) <= 2 * pqbf_size pq /\
    @StaticSemantics.earlyErrors P wr [] = Success false /\
    pattern_no_neg_lookaround wr /\
    no_lower_bound (linden_of wr) /\
    @regex_test naive_params wr flags_ascii (str pq) (pqbf_true pq).
  Proof.
    intros pq WF; exact (pspace_hardness_noneglk_e2e x_char semicolon_char n_char
                           false false false false pq WF n_not_lineterminator_ascii
                           x_not_lineterminator_ascii
                           (x_semicolon_neq_ascii _) (x_n_neq_ascii _)).
  Qed.

  Notation sat_str nv pf := (lexsat_string x_char semicolon_char n_char nv pf) (only parsing).

  Theorem optp_hardness_matcher_ascii: forall nv pf, wf_pos_formula nv pf ->
    let wr := theRegex_w (lexsat_qbf nv pf) x_char semicolon_char in
    pattern_size wr <= 8 * lexsat_size nv pf /\
    length (sat_str nv pf) <= 2 * lexsat_size nv pf /\
    @StaticSemantics.earlyErrors P wr [] = Success false /\
    (pattern_no_lookaround wr /\ pattern_no_lower_bound wr) /\
    (no_lookaround (linden_of wr) /\ no_lower_bound (linden_of wr)) /\
    exists m res,
      @Semantics.compilePattern P wr (rer_at wr) = Success m /\
      m (sat_str nv pf) 0 = Success res /\
      match res with
      | Some ms => is_lex_max_sat nv pf (defined_bits (Notation.MatchState.captures ms))
      | None => forall b, length b = nv -> assign_cnf b pf = false
      end.
  Proof.
    intros nv pf WF; exact (optp_hardness_matcher x_char semicolon_char n_char
                              false false false false nv pf WF (x_semicolon_neq_ascii _)).
  Qed.

  Theorem optp_hardness_e2e_ascii: forall nv pf, wf_pos_formula nv pf ->
    let wr := theRegex_w (lexsat_qbf nv pf) x_char semicolon_char in
    pattern_size wr <= 8 * lexsat_size nv pf /\
    length (sat_str nv pf) <= 2 * lexsat_size nv pf /\
    @StaticSemantics.earlyErrors P wr [] = Success false /\
    (pattern_no_lookaround wr /\ pattern_no_lower_bound wr) /\
    (no_lookaround (linden_of wr) /\ no_lower_bound (linden_of wr)) /\
    exists inst,
      @regExpInitialize P wr flags_ascii = Success inst /\
      match @regExpExec P inst (sat_str nv pf) with
      | Success (Null _) => forall b, length b = nv -> assign_cnf b pf = false
      | Success (Exotic A _) =>
          is_lex_max_sat nv pf (defined_bits (List.tl (ExecArrayExotic.array A)))
      | _ => False
      end.
  Proof.
    intros nv pf WF; exact (optp_hardness_e2e x_char semicolon_char n_char
                              false false false false nv pf WF (x_semicolon_neq_ascii _)).
  Qed.

  Theorem optp_hardness_machine_ascii: forall nv pf, wf_pos_formula nv pf ->
    let r := lexsat_regex x_char semicolon_char nv pf in
    let inp := init_input (sat_str nv pf) in
    let n := guess_budget r inp in
    let rer := rer_at (theRegex_w (lexsat_qbf nv pf) x_char semicolon_char) in
    expanded_size r <= 9 * lexsat_size nv pf /\
    length (sat_str nv pf) <= 2 * lexsat_size nv pf /\
    n <= S (27 * lexsat_size nv pf * (1 + 2 * lexsat_size nv pf)) /\
    (no_lookaround r /\ no_lower_bound r) /\
    exists best,
      parse_spec rer r inp n best /\
      length best = S n /\
      match option_map snd (exec_of_parse rer r inp best) with
      | Some gm => is_lex_max_sat nv pf (bits_of_gm nv gm)
      | None => forall b, length b = nv -> assign_cnf b pf = false
      end.
  Proof.
    intros nv pf WF; exact (optp_hardness_machine x_char semicolon_char n_char _ nv pf WF
                              (x_semicolon_neq_ascii _)).
  Qed.

End AsciiEndToEnd.
