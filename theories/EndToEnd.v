From JsRegexOptp Require Import QbfPrenex RegexEncoding MembershipProof WarblreExtensions
  WarblreEncoding Warblre Qbf Bits GroupMaps RegexEncodingPoslk HardnessProofs HardnessPoslk
  HardnessOptp MembershipOptp.
From JsRegexOptp Require Import Basics.
From Linden Require Import Tree.
From Linden Require Import Chars Groups Semantics LWParameters RegexpTranslation
  FunctionalUtils ResultTranslation EquivMain.
From Warblre Require Import RegExpRecord Base Semantics Frontend Result Patterns Notation Match.
From Stdlib Require Import List Lia BinInt.
Import ListNotations.

Section EndToEnd.
  Context {params: LindenParameters}.

  (* The fuel budget definition; it is a polynomial in the string size and the expanded regex size. *)
  Remark fuel_budget_value:
    forall (r: regex) (inp: input),
      fuel_budget r inp
      = S ((1 + length (input_str inp))
           * (expanded_size r + expanded_size r * expanded_size r)).
  Proof. reflexivity. Qed.

  (* The guess budget definition; it is a polynomial in the string size and the regex size. *)
  Remark guess_budget_value:
    forall (r: regex) (inp: input),
      guess_budget r inp = S (3 * ((1 + remaining_length inp forward) * regex_size r)).
  Proof. reflexivity. Qed.

  (* The definition of regex_test: `regex_test wr flags s b` holds if both of the following are true:
     - matching the Warblre regex `wr` on the string `s` with the flags `flags` does not result in an error,
     - the boolean `b` indicates whether there is a match of `wr` on `s` in the Warblre sense. *)
  Remark regex_test_unfold:
    forall (wr: Patterns.Regex) (flags: RegExpFlags) (s: LWParameters.string) (b: bool),
      regex_test wr flags s b <->
      exists inst res,
        regExpInitialize wr flags = Success inst /\
        RegExpInstance.regExpMatcher inst s 0 = Success res /\
        (res <> None <-> b = true) /\
        ((exists inst', regExpExec inst s = Success (Null inst')) <-> b = false) /\
        ((exists A inst', regExpExec inst s = Success (Exotic A inst')) <-> b = true).
  Proof. intros; split; exact (fun h => h). Qed.

  (* Given a list of choices `cs`, the length of the output of the OptP algorithm with
     the list of choices `cs` is one plus the length of `cs`.
     This is due to the result bit being prepended to the list of choices in the output.*)
  Remark optp_output_width:
    forall (rer: RegExpRecord) (r: regex) (inp: input) (cs: list bool),
      length (optp_output rer r inp cs) = S (length cs).
  Proof. reflexivity. Qed.

  (* We measure the size of a list of actions by expanding its lower-bounded quantifiers
     and giving weight 1 to Acheck and Aclose actions. *)
  Local Notation actions_size := MembershipProof.actions_size.

  (* TODO explain *)
  Theorem membership_state_size_bound:
    forall (wr: Patterns.Regex) (inp: input) (dir: Direction) (act: actions),
      let lr := linden_of wr in
      MembershipProof.act_from_regex lr inp act dir ->
      let n := expanded_size lr in
      let frame := (1 + length (input_str inp)) * actions_size act in
      actions_size act <= n + Nat.div2 (n * S n) /\
      (no_lower_bound lr ->
       fuel_budget lr inp * frame
       <= S (3 * (1 + length (input_str inp)) * pattern_size wr * S (3 * pattern_size wr))
          * ((1 + length (input_str inp))
             * (3 * pattern_size wr * S (3 * pattern_size wr)))).
  Proof.
    intros * AFR; cbv zeta.
    pose proof MembershipProof.actions_size_bound' AFR as ACT.
    split; [exact ACT|intro NLB].
    apply PeanoNat.Nat.mul_le_mono;
      [now apply fuel_budget_source|apply PeanoNat.Nat.mul_le_mono_l].
    pose proof expanded_size_pos lr.
    pose proof expanded_size_nolb lr NLB.
    pose proof (linden_of_size wr: regex_size lr <= pattern_size wr).
    pose proof triangle_even (expanded_size lr).
    nia.
  Qed.

  Corollary compute_result_terminates:
    forall (rer: RegExpRecord) (r: regex) (inp: input) (act: actions) (dir: Direction),
      MembershipProof.act_from_regex r inp act dir ->
      forall fuel, fuel > MembershipProof.actions_fuel inp act dir ->
        forall gm, compute_result rer act inp gm dir fuel <> Out_of_fuel.
  Proof.
    intros rer r inp act dir AFR fuel FUEL gm.
    pose proof MembershipProof.functional_terminates' rer r inp act dir AFR fuel FUEL gm as NN.
    destruct (FunctionalSemantics.compute_tree rer act inp gm dir fuel) as [t|] eqn:CT; [|congruence].
    pose proof MembershipProof.compute_result_correctness _ _ _ _ _ _ _ CT as CORR.
    destruct (compute_result rer act inp gm dir fuel); cbn in CORR; congruence.
  Qed.

  Context (a_char semicolon_char z_char: Parameters.Character).
  Context (hasIndices global ignoreCase multiline dotAll: bool).

  (* We set the `sticky` flag to true (anchored search). *)
  Let flags := reg_exp_flags hasIndices global ignoreCase multiline dotAll tt true.

  (** * PSPACE-hardness results *)
  Section PspaceHardness.
    Context (pq: pqbf).
    (* The PQBF `pq` must be well-formed. *)
    Hypothesis wf_pq: wf_pqbf pq.

    (* The QBF' corresponding to the prenex QBF `pq`. *)
    Let q := qbf_of_pqbf pq.
    (* The regex corresponding to the translation of `q`. *)
    Let wr := theRegex_w q a_char semicolon_char.
    (* The string corresponding to the translation of `q`. *)
    Let s := theString q a_char semicolon_char z_char.
    (* The RegExpRecord corresponding to the flags and the Warblre regex. *)
    Let rer := rer_of wr flags.

    (* We require the canonicalized `a` character to be different from the canonicalized `;` character. *)
    Hypothesis a_semicolon_neq:
      Character.canonicalize rer a_char <> Character.canonicalize rer semicolon_char.

    (* PSPACE-hardness theorem in terms of the Warblre `Matcher`: *)
    Theorem pspace_hardness_matcher:
      (* the size of the regex `wr` is linear in the size of the PQBF, *)
      pattern_size wr <= 8 * pqbf_size pq /\
      (* so is the length of the string, *)
      length s <= 2 * pqbf_size pq /\
      (* the regex passes the early errors check, *)
      StaticSemantics.earlyErrors wr [] = Success false /\
      (* does not have lower-bounded quantifiers, *)
      (pattern_no_lower_bound wr) /\ (no_lower_bound (linden_of wr)) /\
      (* compiling the regex `wr` with the flags `flags` (contained in `rer`) succeeds, *)
      exists m res,
        Semantics.compilePattern wr rer = Success m /\
        (* matching the regex on the string terminates without errors, *)
        m s 0 = Success res /\
        (* and we have a match if and only if the PQBF is true. *)
        (res <> None <-> pqbf_true pq = true).
    Proof.
      split; [rewrite <- qbf_size_of_pqbf; apply theRegex_w_size|].
      split; [rewrite <- qbf_size_of_pqbf; apply theString_size|].
      split; [apply wr_earlyErrors, wf_qbf_of_pqbf, wf_pq|].
      split; [apply theRegex_w_nolb, wf_qbf_of_pqbf, wf_pq|].
      split; [apply wr_nolb, wf_qbf_of_pqbf, wf_pq|].
      rewrite <- (qbf_of_pqbf_true pq).
      apply qbf_regex_warblre_matcher; auto using wf_qbf_of_pqbf.
    Qed.

    (* End-to-end PSPACE-hardness theorem: *)
    Theorem pspace_hardness_e2e:
      (* the size of the regex `wr` is linear in the size of the PQBF, *)
      pattern_size wr <= 8 * pqbf_size pq /\
      (* so is the length of the string, *)
      length s <= 2 * pqbf_size pq /\
      (* the regex passes the early errors check, *)
      StaticSemantics.earlyErrors wr [] = Success false /\
      (* it has no lower-bounded quantifiers, *)
      (pattern_no_lower_bound wr) /\ (no_lower_bound (linden_of wr)) /\
      (* and `wr` has a match on `s` with the flags `flags` if and only if the PQBF `pq` is true. *)
      regex_test wr flags s (pqbf_true pq).
    Proof.
      split; [rewrite <- qbf_size_of_pqbf; apply theRegex_w_size|].
      split; [rewrite <- qbf_size_of_pqbf; apply theString_size|].
      split; [apply wr_earlyErrors, wf_qbf_of_pqbf, wf_pq|].
      split; [apply theRegex_w_nolb, wf_qbf_of_pqbf, wf_pq|].
      split; [apply wr_nolb, wf_qbf_of_pqbf, wf_pq|].
      rewrite <- (qbf_of_pqbf_true pq).
      apply qbf_regex_warblre_frontend_all; auto using wf_qbf_of_pqbf.
    Qed.
  End PspaceHardness.

  (** * PSPACE-hardness results without negative lookarounds *)
  Section PspaceHardnessPoslk.
    Context (pq: pqbf).
    (* The PQBF pq must be well-formed. *)
    Hypothesis wf_pq: wf_pqbf pq.
    (* Neither of the characters a and z must be line terminators. *)
    Hypothesis z_no_line_terminator: ~In z_char Character.line_terminators.
    Hypothesis a_no_line_terminator: ~In a_char Character.line_terminators.

    (* The QBF' corresponding to the prenex QBF `pq`. *)
    Let q := qbf_of_pqbf pq.
    (* The Warblre regex corresponding to the translation of `q` without negative lookarounds. *)
    Let wr := theRegex_poslk_w q a_char semicolon_char z_char.
    (* The string corresponding to the translation of `q`. *)
    Let s := theString q a_char semicolon_char z_char.
    (* The RegExpRecord corresponding to the regex `wr` and the flags `flags`. *)
    Let rer := rer_of wr flags.

    (* We require the canonicalized `a` character to be different from the canonicalized `;` and `z` characters. *)
    Hypothesis a_semicolon_neq:
      Character.canonicalize rer a_char <> Character.canonicalize rer semicolon_char.
    Hypothesis a_z_neq:
      Character.canonicalize rer a_char <> Character.canonicalize rer z_char.

    (* PSPACE-hardness theorem without negative lookarounds, in terms of the Warblre `Matcher`: *)
    Theorem pspace_hardness_noneglk_matcher:
      (* the size of the regex `wr` is linear in the size of the PQBF `pq`, *)
      pattern_size wr <= 25 * pqbf_size pq /\
      (* so is the length of the string `s`, *)
      length s <= 2 * pqbf_size pq /\
      (* the regex passes the early errors check, *)
      StaticSemantics.earlyErrors wr [] = Success false /\
      (* has no negative lookarounds nor lower-bounded quantifiers, *)
      (pattern_no_neg_lookaround wr /\ pattern_no_lower_bound wr) /\
      (no_neg_lookaround (linden_of wr) /\ no_lower_bound (linden_of wr)) /\
      (* compiling the regex `wr` with the flags `flags` (contained in `rer`) succeeds, *)
      exists m res,
        Semantics.compilePattern wr rer = Success m /\
        (* matching `wr` on `s` terminates without an error, *)
        m s 0 = Success res /\
        (* and `wr` has a match on `s` if and only if the PQBF `pq` is true. *)
        (res <> None <-> pqbf_true pq = true).
    Proof.
      split; [rewrite <- qbf_size_of_pqbf; apply theRegex_poslk_w_size|].
      split; [rewrite <- qbf_size_of_pqbf; apply theString_size|].
      split; [apply wr_poslk_earlyErrors, wf_qbf_of_pqbf, wf_pq|].
      split; [split; [apply theRegex_poslk_w_noneglk | apply theRegex_poslk_w_nolb];
              apply wf_qbf_of_pqbf, wf_pq|].
      split; [split; [apply wr_poslk_noneglk | apply wr_poslk_nolb];
              apply wf_qbf_of_pqbf, wf_pq|].
      rewrite <- (qbf_of_pqbf_true pq).
      apply qbf_poslk_warblre_matcher; auto using wf_qbf_of_pqbf.
    Qed.

    (* End-to-end PSPACE-hardness theorem without negative lookarounds: *)
    Theorem pspace_hardness_noneglk_e2e:
      (* the size of the regex `wr` is linear in the size of the PQBF `pq`, *)
      pattern_size wr <= 25 * pqbf_size pq /\
      (* so is the length of the string `s`, *)
      length s <= 2 * pqbf_size pq /\
      (* the regex `wr` passes the early errors check, *)
      StaticSemantics.earlyErrors wr [] = Success false /\
      (* does not have negative lookarounds nor lower-bounded quantifiers, *)
      (pattern_no_neg_lookaround wr /\ pattern_no_lower_bound wr) /\
      (no_neg_lookaround (linden_of wr) /\ no_lower_bound (linden_of wr)) /\
      (* and `wr` has a match on `s` with the flags `flags` if and only if the PQBF `pq` is true. *)
      regex_test wr flags s (pqbf_true pq).
    Proof.
      split; [rewrite <- qbf_size_of_pqbf; apply theRegex_poslk_w_size|].
      split; [rewrite <- qbf_size_of_pqbf; apply theString_size|].
      split; [apply wr_poslk_earlyErrors, wf_qbf_of_pqbf, wf_pq|].
      split; [split; [apply theRegex_poslk_w_noneglk | apply theRegex_poslk_w_nolb];
              apply wf_qbf_of_pqbf, wf_pq|].
      split; [split; [apply wr_poslk_noneglk | apply wr_poslk_nolb];
              apply wf_qbf_of_pqbf, wf_pq|].
      rewrite <- (qbf_of_pqbf_true pq).
      apply qbf_poslk_warblre_frontend_all; auto using wf_qbf_of_pqbf.
    Qed.
  End PspaceHardnessPoslk.

  (** * PSPACE-membership results *)
  Section PspaceMembership.
    (* We give ourselves a regex that passes the early errors check. *)
    Context (wr: Patterns.Regex).
    Hypothesis no_early_errors: StaticSemantics.earlyErrors wr [] = Success false.

    (* The RegExpRecord corresponding to matching `wr` with the flags `flags`. *)
    Let rer := rer_of wr flags.
    (* The translation of `wr` into a Linden regex. *)
    Let lr := linden_of wr.

    (* PSPACE-membership theorem in terms of the Warblre `Matcher`: *)
    Theorem pspace_membership_matcher:
      (* for any input `inp` (an input string and an index into that string), *)
      forall (inp: input),
        (* - if the regex has no lower-bounded quantifiers, then the fuel budget corresponding to matching the regex on the string is polynomial in the input and regex sizes, *)
        (no_lower_bound lr ->
         fuel_budget lr inp
         <= S (3 * (1 + length (input_str inp)) * pattern_size wr
               * S (3 * pattern_size wr))) /\
        exists m lf,
          (* - compiling the regex `wr` into a Warblre `Matcher` succeeds, *)
          Semantics.compilePattern wr rer = Success m /\
          (* - matching `wr` on `inp` according to the Warblre specification terminates without errors, yielding a result `lf`... *)
          m (input_str inp) (idx inp)
            = Success (to_MatchState lf (RegExpRecord.capturingGroupsCount rer)) /\
          (* ... that corresponds to the result of the PSPACE algorithm run from `inp` with the fuel budget. *)
          res_to_leaf (compute_result rer [Areg lr] inp GroupMap.empty forward
                         (fuel_budget lr inp)) = Some lf.
    Proof.
      intro inp.
      split; [apply fuel_budget_source|].
      destruct (matcher_at_input wr rer no_early_errors eq_refl) as [m (COMP & MATCH)].
      exists m, (linden_result rer lr inp); eauto using compute_result_poly.
    Qed.

    (* End-to-end PSPACE-membership theorem: *)
    Theorem pspace_membership_e2e:
      (* for any input string, *)
      forall (s: LWParameters.string),
        let inp := init_input s in
        (* - if the regex does not have lower-bounded quantifiers, then the fuel budget corresponding to matching the regex on the string is polynomial in the regex and string sizes, *)
        (no_lower_bound lr ->
         fuel_budget lr inp
         <= S (3 * (1 + length s) * pattern_size wr * S (3 * pattern_size wr))) /\
        exists inst lf,
          (* - compiling the regex in the Warblre sense succeeds (this is most of what regExpInitialize does), *)
          regExpInitialize wr flags = Success inst /\
          (* - running the PSPACE algorithm with the fuel budget, the regex `lr` and the string `s` succeeds, yielding a result `lf`... *)
          res_to_leaf (compute_result rer [Areg lr] inp GroupMap.empty forward
                         (fuel_budget lr inp)) = Some lf /\
          (* ... that matches the Warblre result of matching `wr` on `s`. *)
          exec_agrees inst s (to_MatchState lf (RegExpRecord.capturingGroupsCount rer)).
    Proof.
      intros s inp.
      split; [apply (fuel_budget_source wr inp)|].
      destruct (matches_regExpExec_result_flags wr lr s no_early_errors eq_refl flags rer
                  eq_refl eq_refl) as [inst [INIT RES]].
      exists inst, (linden_result rer lr inp).
      split; [exact INIT|]; split; [apply compute_result_poly; reflexivity | exact RES].
    Qed.
  End PspaceMembership.

  (** * OptP-hardness results *)
  Section OptpHardness.
    (* `nv` is the number of variables, `pf` is a CNF propositional formula. *)
    Context (nv: nat) (pf: pos_formula).
    (* We assume that the propositional formula `pf` is well-formed (that all its literals use variables between 1 and `nv`). *)
    Hypothesis wf_pf: wf_pos_formula nv pf.
    (* We assume that each of the `nv` variables occurs in `pf`. *)
    Hypothesis uses_all_pf: uses_all_vars nv pf.

    (* The Warblre regex corresponding to translating the formula `pf` into an instance of regex matching.
       We reuse the QBF translation by prepending existential quantifiers to the formula (this is what lexsat_qbf does). *)
    Let wr := theRegex_w (lexsat_qbf nv pf) a_char semicolon_char.
    (* The string corresponding to translating the formula `pf` into an instance of regex matching. *)
    Let s := lexsat_string a_char semicolon_char z_char nv pf.
    (* The RegExpRecord corresponding to matching the regex `wr` with the flags `flags`. *)
    Let rer := rer_of wr flags.

    (* We require the canonicalized `a` character to differ from the canonicalized `;` character. *)
    Hypothesis a_semicolon_neq:
      Character.canonicalize rer a_char <> Character.canonicalize rer semicolon_char.

    (* OptP-hardness theorem in terms of the Warblre `Matcher`: *)
    Theorem optp_hardness_matcher:
      (* the size of the regex `wr` is linear in the size of the LEXICOGRAPHIC SAT formula `pf`, *)
      pattern_size wr <= 11 * pos_formula_size pf /\
      (* so is the length of the string `s`, *)
      length s <= 2 * pos_formula_size pf /\
      (* the regex `wr` passes the early errors check, *)
      StaticSemantics.earlyErrors wr [] = Success false /\
      (* does not have lookarounds nor lower-bounded quantifiers in the Warblre sense, *)
      (pattern_no_lookaround wr /\ pattern_no_lower_bound wr) /\
      (* nor in the Linden sense, *)
      (no_lookaround (linden_of wr) /\ no_lower_bound (linden_of wr)) /\
      exists m res,
        (* compiling the regex `wr` succeeds, *)
        Semantics.compilePattern wr rer = Success m /\
        (* matching the regex `wr` on the string `s` terminates without errors, *)
        m s 0 = Success res /\
        (* and: *)
        match res with
        (* - if there is a match of `wr` on `s`, then the capture groups of the highest priority
           match encode the solution to the original LEXICOGRAPHIC SAT instance, *)
        | Some ms => is_lex_max_sat nv pf (defined_bits (Notation.MatchState.captures ms))
        (* - otherwise, the original LEXICOGRAPHIC SAT instance has no solution. *)
        | None => forall b, length b = nv -> assign_cnf b pf = false
        end.
    Proof.
      split; [now apply lexsat_w_size_bound|].
      split; [now apply lexsat_string_size_bound|].
      split; [exact (lexsat_w_earlyErrors a_char semicolon_char nv pf wf_pf)|].
      split; [split; [apply lexsat_w_nolk | apply lexsat_w_nolb]; exact wf_pf|].
      split; [exact (lexsat_w_frag a_char semicolon_char nv pf wf_pf)|].
      destruct (lexsat_w_matcher _ _ nv pf wf_pf z_char rer eq_refl) as [m (COMP & EXEC)].
      do 2 eexists; split; [exact COMP|]; split; [exact EXEC | now apply lexsat_answer].
    Qed.

    (* End-to-end OptP-hardness theorem: *)
    Theorem optp_hardness_e2e:
      (* the size of the regex `wr` is linear in the size of the LEXICOGRAPHIC SAT formula `pf`, *)
      pattern_size wr <= 11 * pos_formula_size pf /\
      (* so is the length of the string `s`, *)
      length s <= 2 * pos_formula_size pf /\
      (* the regex `wr` passes the early errors check, *)
      StaticSemantics.earlyErrors wr [] = Success false /\
      (* does not have lookarounds nor lower-bounded quantifiers in the Warblre sense, *)
      (pattern_no_lookaround wr /\ pattern_no_lower_bound wr) /\
      (* nor in the Linden sense, *)
      (no_lookaround (linden_of wr) /\ no_lower_bound (linden_of wr)) /\
      exists inst,
        (* compiling the Warblre regex `wr` succeeds (this is essentially what regExpInitialize does), *)
        regExpInitialize wr flags = Success inst /\
        (* and: *)
        match regExpExec inst s with
        (* - if there is no match of `wr` on `s`, then there is no solution to the original LEXICOGRAPHIC SAT instance, *)
        | Success (Null _) => forall b, length b = nv -> assign_cnf b pf = false
        (* - otherwise, the capture groups of the highest priority match encode the solution to the
           original LEXICOGRAPHIC SAT instance. *)
        | Success (Exotic A _) =>
            is_lex_max_sat nv pf (defined_bits (List.tl (ExecArrayExotic.array A)))
        (* - No error ever occurs during matching. *)
        | _ => False
        end.
    Proof.
      split; [now apply lexsat_w_size_bound|].
      split; [now apply lexsat_string_size_bound|].
      split; [exact (lexsat_w_earlyErrors a_char semicolon_char nv pf wf_pf)|].
      split; [split; [apply lexsat_w_nolk | apply lexsat_w_nolb]; exact wf_pf|].
      split; [exact (lexsat_w_frag a_char semicolon_char nv pf wf_pf)|].
      destruct (lexsat_w_exec_result a_char semicolon_char nv pf wf_pf z_char flags rer
                  eq_refl eq_refl) as [inst [INIT RES]].
      exists inst; split; [exact INIT | eapply exec_array_transfer; [exact RES|]].
      now apply (lexsat_answer_flags a_char semicolon_char z_char flags rer nv pf
                   wf_pf a_semicolon_neq eq_refl).
    Qed.
  End OptpHardness.

  (* OptP-hardness theorem, more formally: *)
  Theorem optp_hardness_machine:
    forall (rer: RegExpRecord) nv pf,
      (* Let `pf` be a well-formed propositional formula with `nv` variables. *)
      wf_pos_formula nv pf ->
      (* Assume that each of the `nv` variables occurs in `pf`. *)
      uses_all_vars nv pf ->
      (* Assume that the canonicalized `a` and `;` characters are different. *)
      Character.canonicalize rer a_char <> Character.canonicalize rer semicolon_char ->
      (* Let (r, s) be the instance of regex matching corresponding to `pf`, where `r` is a Linden regex. *)
      let r := lexsat_regex a_char semicolon_char nv pf in
      let s := lexsat_string a_char semicolon_char z_char nv pf in
      let inp := init_input s in
      (* Let `n` be the guess budget corresponding to matching `r` on `s`. *)
      let n := guess_budget r inp in
      (* Then:
         - the sizes of `r` and `s` are linear in the size of `pf`, *)
      expanded_size r <= 12 * pos_formula_size pf /\
      length s <= 2 * pos_formula_size pf /\
      (* - the budget is polynomial in the size of `pf`, *)
      n <= S (33 * pos_formula_size pf * (1 + 2 * pos_formula_size pf)) /\
      (* - `r` has neither lookarounds nor lower-bounded quantifiers, *)
      (no_lookaround r /\ no_lower_bound r) /\
      (* - there exists a result `best` of the OptP algorithm on `r` and `s`, *)
      exists best,
        parse_spec rer r inp n best /\
        (* of size `n+1`, *)
        length best = S n /\
        (* and we can recover the result of the original instance of LEXICOGRAPHIC SAT from `best`,
           by first recovering the capture groups from `best`: *)
        match option_map snd (exec_of_parse rer r inp best) with
        (* - if `best` encodes a successful match, then we can recover the solution of the original
        instance of LEXICOGRAPHIC SAT from the corresponding capture groups, *)
        | Some gm => is_lex_max_sat nv pf (bits_of_gm nv gm)
        (* - otherwise, the original instance of LEXICOGRAPHIC SAT has no solution. *)
        | None => forall b, length b = nv -> assign_cnf b pf = false
        end.
  Proof.
    intros * WF USES NEQ; cbv zeta.
    split; [now apply lexsat_regex_size_bound|].
    split; [now apply lexsat_string_size_bound|].
    split; [now apply lexsat_guess_budget_bound|].
    split; [exact (lexsat_regex_frag a_char semicolon_char nv pf)|].
    destruct (lexsat_by_optp a_char semicolon_char _ (lexsat_qbf_wf nv pf WF) pf eq_refl
                ltac:(intros qt IN; eapply repeat_spec, IN) z_char rer NEQ _
                (compute_tr_is_tree _)) as [best JOIN].
    rewrite lexsat_qbf_num_vars in JOIN; eauto.
  Qed.

  (* OptP-hardness theorem in terms of the OptP machine and the ECMAScript pattern: *)
  Theorem optp_hardness_machine_w:
    forall (rer: RegExpRecord) nv pf,
      (* Let `pf` be a well-formed propositional formula with `nv` variables. *)
      wf_pos_formula nv pf ->
      (* Assume that each of the `nv` variables occurs in `pf`. *)
      uses_all_vars nv pf ->
      (* Assume that the canonicalized `a` and `;` characters are different. *)
      Character.canonicalize rer a_char <> Character.canonicalize rer semicolon_char ->
      (* Let (wr, s) be the instance of regex matching corresponding to `pf`,
         where `wr` is a Warblre (ECMAScript) regex. *)
      let wr := theRegex_w (lexsat_qbf nv pf) a_char semicolon_char in
      let s := lexsat_string a_char semicolon_char z_char nv pf in
      let inp := init_input s in
      (* Let `n` be the guess budget corresponding to matching `wr` on `s`. *)
      let n := guess_budget (linden_of wr) inp in
      (* Then:
         - the sizes of `wr` and `s` are linear in the size of `pf`, *)
      pattern_size wr <= 11 * pos_formula_size pf /\
      length s <= 2 * pos_formula_size pf /\
      (* - the budget is polynomial in the size of `pf`, *)
      n <= S (33 * pos_formula_size pf * (1 + 2 * pos_formula_size pf)) /\
      (* - the regex `wr` passes the early errors check, *)
      StaticSemantics.earlyErrors wr [] = Success false /\
      (* - `wr` has neither lookarounds nor lower-bounded quantifiers, *)
      (pattern_no_lookaround wr /\ pattern_no_lower_bound wr) /\
      (no_lookaround (linden_of wr) /\ no_lower_bound (linden_of wr)) /\
      (* - there exists a result `best` of the OptP algorithm on `wr` and `s`, *)
      exists best,
        parse_spec rer (linden_of wr) inp n best /\
        (* of size `n+1`, *)
        length best = S n /\
        (* and we can recover the result of the original instance of LEXICOGRAPHIC SAT from `best`,
           by first recovering the capture groups from `best`: *)
        match option_map snd (exec_of_parse rer (linden_of wr) inp best) with
        (* - if `best` encodes a successful match, then we can recover the solution of the original
        instance of LEXICOGRAPHIC SAT from the corresponding capture groups, *)
        | Some gm => is_lex_max_sat nv pf (bits_of_gm nv gm)
        (* - otherwise, the original instance of LEXICOGRAPHIC SAT has no solution. *)
        | None => forall b, length b = nv -> assign_cnf b pf = false
        end.
  Proof.
    intros * WF USES NEQ; cbv zeta.
    rewrite <- (lexsat_w_to_linden a_char semicolon_char nv pf WF).
    destruct (optp_hardness_machine rer nv pf WF USES NEQ)
      as (RS & SS & BUD & FRAG & MACHINE).
    split; [now apply lexsat_w_size_bound|].
    split; [exact SS|]; split; [exact BUD|].
    split; [exact (lexsat_w_earlyErrors a_char semicolon_char nv pf WF)|].
    split; [split; [apply lexsat_w_nolk | apply lexsat_w_nolb]; exact WF|].
    split; [exact FRAG | exact MACHINE].
  Qed.

  (** * OptP-membership results *)
  Section OptpMembership.
    (* Let `wr` be a regex that passes the early errors check. *)
    Context (wr: Patterns.Regex).
    Hypothesis no_early_errors: StaticSemantics.earlyErrors wr [] = Success false.

    (* The RegExpRecord corresponding to matching `wr` with the flags `flags`. *)
    Let rer := rer_of wr flags.
    (* The Linden equivalent of `wr`. *)
    Let lr := linden_of wr.

    (* We assume that the regex has neither lookarounds nor lower-bounded quantifiers. *)
    Hypothesis lr_nolk: no_lookaround lr.
    Hypothesis lr_nolb: no_lower_bound lr.

    (* OptP-membership theorem in terms of the Warblre `Matcher`: *)
    Theorem optp_membership_matcher:
      (* Let `inp` be an input (an input string and an index into that string). *)
      forall (inp: input),
        (* Let `n` be the guess budget corresponding to matching `lr` on `inp`. *)
        let n := guess_budget lr inp in
        (* Then:
           - `n` is polynomial in the remaining length of `inp` and the size of `wr`, *)
        n <= S (3 * (1 + remaining_length inp forward) * pattern_size wr) /\
        exists m best,
          (* - compiling `wr` succeeds, *)
          Semantics.compilePattern wr rer = Success m /\
          (* - and there exists a result `best` of the OptP algorithm, *)
          parse_spec rer lr inp n best /\
          (* of length `n+1`, *)
          length best = S n /\
          (* such that `best` corresponds to the Warblre result of matching `wr` on `inp`. *)
          m (input_str inp) (idx inp)
            = Success (to_MatchState (exec_of_parse rer lr inp best)
                                     (RegExpRecord.capturingGroupsCount rer)).
    Proof.
      intros inp ?.
      split; [apply guess_budget_source|].
      destruct (optp_membership_poly rer lr inp _ lr_nolk lr_nolb (compute_tr_is_tree _))
        as [best (PARSE & LEN & EXECP)].
      destruct (matcher_at_input wr rer no_early_errors eq_refl) as [m (COMP & MATCH)].
      exists m, best; rewrite MATCH, EXECP; auto 10.
    Qed.

    (* End-to-end OptP-membership theorem: *)
    Theorem optp_membership_e2e:
      (* Let `s` be an input string. *)
      forall (s: LWParameters.string),
        let inp := init_input s in
        (* Let `n` be the guess budget corresponding to matching `lr` on `s`. *)
        let n := guess_budget lr inp in
        (* Then:
           - `n` is polynomial in the length of `s` and the size of `wr`, *)
        n <= S (3 * (1 + length s) * pattern_size wr) /\
        exists inst best,
          (* - compiling `wr` succeeds (this is essentially what `regExpInitialize` does), *)
          regExpInitialize wr flags = Success inst /\
          (* - and there exists a result `best` of the OptP algorithm, *)
          parse_spec rer lr inp n best /\
          (* of length `n+1`, *)
          length best = S n /\
          (* that corresponds to the Warblre result of matching `wr` on `s`. *)
          exec_agrees inst s (to_MatchState (exec_of_parse rer lr inp best)
                                            (RegExpRecord.capturingGroupsCount rer)).
    Proof.
      intros s inp ?.
      split; [apply (guess_budget_source wr inp)|].
      destruct (optp_membership_poly rer lr inp _ lr_nolk lr_nolb (compute_tr_is_tree _))
        as [best OPTP].
      destruct (matches_regExpExec_result_flags wr lr s no_early_errors eq_refl flags rer
                  eq_refl eq_refl) as [inst [INIT RES]]; destruct OPTP as (? & ? & EXECP).
      exists inst, best; unfold linden_result, first_leaf in RES; rewrite EXECP; auto 10.
    Qed.
  End OptpMembership.

End EndToEnd.

Definition end_to_end_results :=
  (@fuel_budget_value, @guess_budget_value, @regex_test_unfold, @optp_output_width,
   @pspace_hardness_matcher, @pspace_hardness_e2e, @pspace_hardness_noneglk_matcher,
   @pspace_hardness_noneglk_e2e, @pspace_membership_matcher, @pspace_membership_e2e,
   @membership_state_size_bound, @compute_result_terminates,
   @optp_hardness_matcher, @optp_hardness_e2e,
   @optp_hardness_machine, @optp_hardness_machine_w, @optp_membership_matcher,
   @optp_membership_e2e).
Print Assumptions end_to_end_results.
