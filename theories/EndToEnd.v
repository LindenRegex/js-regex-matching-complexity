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

  Remark fuel_budget_value:
    forall (r: regex) (inp: input),
      fuel_budget r inp = S ((1 + length (input_str inp)) * expanded_size r).
  Proof. reflexivity. Qed.

  Remark guess_budget_value:
    forall (r: regex) (inp: input),
      guess_budget r inp = S (3 * ((1 + remaining_length inp forward) * regex_size r)).
  Proof. reflexivity. Qed.

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

  Remark optp_output_width:
    forall (rer: RegExpRecord) (r: regex) (inp: input) (cs: list bool),
      length (optp_output rer r inp cs) = S (length cs).
  Proof. reflexivity. Qed.

  Local Notation actions_size := (MembershipProof.act_wt expanded_size 1).

  Theorem membership_state_size_bound:
    forall (wr: Patterns.Regex) (inp: input) (dir: Direction) (r: regex) (act: actions),
      let lr := linden_of wr in
      expanded_size r <= expanded_size lr ->
      MembershipProof.act_from_regex r dir act ->
      let n := expanded_size lr in
      let acts := n + Nat.div2 (n * S n) in
      let frame := (1 + length (input_str inp)) * actions_size act in
      actions_size act <= acts /\
      (forall lk rlk, In (Areg (Lookaround lk rlk)) act ->
                      expanded_size rlk <= expanded_size lr) /\
      (no_lower_bound lr ->
       fuel_budget lr inp * frame
       <= S (3 * (1 + length (input_str inp)) * pattern_size wr)
          * ((1 + length (input_str inp))
             * (3 * pattern_size wr * S (3 * pattern_size wr)))).
  Proof.
    intros * LE AFR; cbv zeta.
    pose proof MembershipProof.actions_size_bound' AFR as ACT; cbv zeta in ACT.
    pose proof MembershipProof.chunk_bound AFR as OK.
    pose proof triangle_even (expanded_size r).
    pose proof triangle_even (expanded_size lr).
    assert (ACTS: actions_size act <= expanded_size lr
                                      + Nat.div2 (expanded_size lr * S (expanded_size lr)))
      by nia.
    split; [exact ACTS|split].
    - clear -LE OK; intros lk rlk IN; revert IN.
      induction OK as [_|a l CH _ IH]; intro IN; [contradiction|].
      simpl in IN; destruct IN as [->|IN]; [|now auto].
      unfold MembershipProof.chunk_ok in CH; simpl in CH; lia.
    - intro NLB.
      apply PeanoNat.Nat.mul_le_mono;
        [now apply fuel_budget_source|apply PeanoNat.Nat.mul_le_mono_l].
      pose proof MembershipProof.expanded_size_pos lr.
      pose proof expanded_size_nolb lr NLB.
      pose proof (linden_of_size wr: regex_size lr <= pattern_size wr).
      nia.
  Qed.

  Context (x_char semicolon_char n_char: Parameters.Character).
  Context (global ignoreCase multiline dotAll: bool).

  Let flags := reg_exp_flags false global ignoreCase multiline dotAll tt true.

  Section PspaceHardness.
    Context (pq: pqbf).
    Hypothesis wf_pq: wf_pqbf pq.

    Let q := qbf_of_pqbf pq.
    Let wr := theRegex_w q x_char semicolon_char.
    Let s := theString q x_char semicolon_char n_char.
    Let rer := rer_of wr flags.

    Hypothesis x_semicolon_neq:
      Character.canonicalize rer x_char <> Character.canonicalize rer semicolon_char.

    Theorem pspace_hardness_matcher:
      pattern_size wr <= 8 * pqbf_size pq /\
      length s <= 2 * pqbf_size pq /\
      StaticSemantics.earlyErrors wr [] = Success false /\
      no_lower_bound (linden_of wr) /\
      exists m res,
        Semantics.compilePattern wr rer = Success m /\
        m s 0 = Success res /\
        (res <> None <-> pqbf_true pq = true).
    Proof.
      split; [rewrite <- qbf_size_of_pqbf; apply theRegex_w_size|].
      split; [rewrite <- qbf_size_of_pqbf; apply theString_size|].
      split; [apply wr_earlyErrors, wf_qbf_of_pqbf, wf_pq|].
      split; [apply wr_nolb, wf_qbf_of_pqbf, wf_pq|].
      rewrite <- (qbf_of_pqbf_true pq).
      apply qbf_regex_warblre_matcher; auto using wf_qbf_of_pqbf.
    Qed.

    Theorem pspace_hardness_e2e:
      pattern_size wr <= 8 * pqbf_size pq /\
      length s <= 2 * pqbf_size pq /\
      StaticSemantics.earlyErrors wr [] = Success false /\
      no_lower_bound (linden_of wr) /\
      regex_test wr flags s (pqbf_true pq).
    Proof.
      split; [rewrite <- qbf_size_of_pqbf; apply theRegex_w_size|].
      split; [rewrite <- qbf_size_of_pqbf; apply theString_size|].
      split; [apply wr_earlyErrors, wf_qbf_of_pqbf, wf_pq|].
      split; [apply wr_nolb, wf_qbf_of_pqbf, wf_pq|].
      rewrite <- (qbf_of_pqbf_true pq).
      apply qbf_regex_warblre_frontend_all; auto using wf_qbf_of_pqbf.
    Qed.
  End PspaceHardness.

  Section PspaceHardnessPoslk.
    Context (pq: pqbf).
    Hypothesis wf_pq: wf_pqbf pq.
    Hypothesis n_no_line_terminator: ~In n_char Character.line_terminators.
    Hypothesis x_no_line_terminator: ~In x_char Character.line_terminators.

    Let q := qbf_of_pqbf pq.
    Let wr := theRegex_poslk_w q x_char semicolon_char n_char.
    Let s := theString q x_char semicolon_char n_char.
    Let rer := rer_of wr flags.

    Hypothesis x_semicolon_neq:
      Character.canonicalize rer x_char <> Character.canonicalize rer semicolon_char.
    Hypothesis x_n_neq:
      Character.canonicalize rer x_char <> Character.canonicalize rer n_char.

    Theorem pspace_hardness_noneglk_matcher:
      pattern_size wr <= 25 * pqbf_size pq /\
      length s <= 2 * pqbf_size pq /\
      StaticSemantics.earlyErrors wr [] = Success false /\
      pattern_no_neg_lookaround wr /\
      no_lower_bound (linden_of wr) /\
      exists m res,
        Semantics.compilePattern wr rer = Success m /\
        m s 0 = Success res /\
        (res <> None <-> pqbf_true pq = true).
    Proof.
      split; [rewrite <- qbf_size_of_pqbf; apply theRegex_poslk_w_size|].
      split; [rewrite <- qbf_size_of_pqbf; apply theString_size|].
      split; [apply wr_poslk_earlyErrors, wf_qbf_of_pqbf, wf_pq|].
      split; [apply theRegex_poslk_w_noneglk, wf_qbf_of_pqbf, wf_pq|].
      split; [apply wr_poslk_nolb, wf_qbf_of_pqbf, wf_pq|].
      rewrite <- (qbf_of_pqbf_true pq).
      apply qbf_poslk_warblre_matcher; auto using wf_qbf_of_pqbf.
    Qed.

    Theorem pspace_hardness_noneglk_e2e:
      pattern_size wr <= 25 * pqbf_size pq /\
      length s <= 2 * pqbf_size pq /\
      StaticSemantics.earlyErrors wr [] = Success false /\
      pattern_no_neg_lookaround wr /\
      no_lower_bound (linden_of wr) /\
      regex_test wr flags s (pqbf_true pq).
    Proof.
      split; [rewrite <- qbf_size_of_pqbf; apply theRegex_poslk_w_size|].
      split; [rewrite <- qbf_size_of_pqbf; apply theString_size|].
      split; [apply wr_poslk_earlyErrors, wf_qbf_of_pqbf, wf_pq|].
      split; [apply theRegex_poslk_w_noneglk, wf_qbf_of_pqbf, wf_pq|].
      split; [apply wr_poslk_nolb, wf_qbf_of_pqbf, wf_pq|].
      rewrite <- (qbf_of_pqbf_true pq).
      apply qbf_poslk_warblre_frontend_all; auto using wf_qbf_of_pqbf.
    Qed.
  End PspaceHardnessPoslk.

  Section PspaceMembership.
    Context (wr: Patterns.Regex).
    Hypothesis no_early_errors: StaticSemantics.earlyErrors wr [] = Success false.

    Let rer := rer_of wr flags.
    Let lr := linden_of wr.

    Theorem pspace_membership_matcher:
      forall (inp: input),
        (no_lower_bound lr ->
         fuel_budget lr inp <= S (3 * (1 + length (input_str inp)) * pattern_size wr)) /\
        exists m lf,
          Semantics.compilePattern wr rer = Success m /\
          m (input_str inp) (idx inp)
            = Success (to_MatchState lf (RegExpRecord.capturingGroupsCount rer)) /\
          res_to_leaf (pspace_algo rer [Areg lr] inp GroupMap.empty forward
                         (fuel_budget lr inp)) = Some lf.
    Proof.
      intro inp.
      split; [apply fuel_budget_source|].
      destruct (matcher_at_input wr rer no_early_errors eq_refl) as [m (COMP & MATCH)].
      exists m, (linden_result rer lr inp); eauto using pspace_algo_poly.
    Qed.

    Theorem pspace_membership_e2e:
      forall (s: LWParameters.string),
        let inp := init_input s in
        (no_lower_bound lr -> fuel_budget lr inp <= S (3 * (1 + length s) * pattern_size wr)) /\
        exists inst lf,
          regExpInitialize wr flags = Success inst /\
          res_to_leaf (pspace_algo rer [Areg lr] inp GroupMap.empty forward
                         (fuel_budget lr inp)) = Some lf /\
          exec_agrees inst s (to_MatchState lf (RegExpRecord.capturingGroupsCount rer)).
    Proof.
      intros s inp.
      split; [apply (fuel_budget_source wr inp)|].
      destruct (matches_regExpExec_result_flags wr lr s no_early_errors eq_refl flags rer
                  eq_refl eq_refl eq_refl) as [inst [INIT RES]].
      exists inst, (linden_result rer lr inp).
      split; [exact INIT|]; split; [apply pspace_algo_poly; reflexivity | exact RES].
    Qed.
  End PspaceMembership.

  Section OptpHardness.
    Context (nv: nat) (pf: pos_formula).
    Hypothesis wf_pf: wf_pos_formula nv pf.

    Let wr := theRegex_w (lexsat_qbf nv pf) x_char semicolon_char.
    Let s := lexsat_string x_char semicolon_char n_char nv pf.
    Let rer := rer_of wr flags.

    Hypothesis x_semicolon_neq:
      Character.canonicalize rer x_char <> Character.canonicalize rer semicolon_char.

    Theorem optp_hardness_matcher:
      pattern_size wr <= 8 * lexsat_size nv pf /\
      length s <= 2 * lexsat_size nv pf /\
      StaticSemantics.earlyErrors wr [] = Success false /\
      (pattern_no_lookaround wr /\ pattern_no_lower_bound wr) /\
      (no_lookaround (linden_of wr) /\ no_lower_bound (linden_of wr)) /\
      exists m res,
        Semantics.compilePattern wr rer = Success m /\
        m s 0 = Success res /\
        match res with
        | Some ms => is_lex_max_sat nv pf (defined_bits (Notation.MatchState.captures ms))
        | None => forall b, length b = nv -> assign_cnf b pf = false
        end.
    Proof.
      split; [rewrite <- lexsat_qbf_size; apply theRegex_w_size|].
      split; [rewrite <- lexsat_qbf_size; apply theString_size|].
      split; [exact (lexsat_w_earlyErrors x_char semicolon_char nv pf wf_pf)|].
      split; [split; [apply lexsat_w_nolk | apply lexsat_w_nolb]; exact wf_pf|].
      split; [exact (lexsat_w_frag x_char semicolon_char nv pf wf_pf)|].
      destruct (lexsat_w_matcher _ _ nv pf wf_pf n_char rer eq_refl) as [m (COMP & EXEC)].
      do 2 eexists; split; [exact COMP|]; split; [exact EXEC | now apply lexsat_answer].
    Qed.

    Theorem optp_hardness_e2e:
      pattern_size wr <= 8 * lexsat_size nv pf /\
      length s <= 2 * lexsat_size nv pf /\
      StaticSemantics.earlyErrors wr [] = Success false /\
      (pattern_no_lookaround wr /\ pattern_no_lower_bound wr) /\
      (no_lookaround (linden_of wr) /\ no_lower_bound (linden_of wr)) /\
      exists inst,
        regExpInitialize wr flags = Success inst /\
        match regExpExec inst s with
        | Success (Null _) => forall b, length b = nv -> assign_cnf b pf = false
        | Success (Exotic A _) =>
            is_lex_max_sat nv pf (defined_bits (List.tl (ExecArrayExotic.array A)))
        | _ => False
        end.
    Proof.
      split; [rewrite <- lexsat_qbf_size; apply theRegex_w_size|].
      split; [rewrite <- lexsat_qbf_size; apply theString_size|].
      split; [exact (lexsat_w_earlyErrors x_char semicolon_char nv pf wf_pf)|].
      split; [split; [apply lexsat_w_nolk | apply lexsat_w_nolb]; exact wf_pf|].
      split; [exact (lexsat_w_frag x_char semicolon_char nv pf wf_pf)|].
      destruct (lexsat_w_exec_result x_char semicolon_char nv pf wf_pf n_char flags rer
                  eq_refl eq_refl eq_refl) as [inst [INIT RES]].
      exists inst; split; [exact INIT | eapply exec_array_transfer; [exact RES|]].
      now apply (lexsat_answer_flags x_char semicolon_char n_char flags rer nv pf
                   wf_pf x_semicolon_neq eq_refl).
    Qed.
  End OptpHardness.

  Theorem optp_hardness_machine:
    forall (rer: RegExpRecord) nv pf,
      wf_pos_formula nv pf ->
      Character.canonicalize rer x_char <> Character.canonicalize rer semicolon_char ->
      let r := lexsat_regex x_char semicolon_char nv pf in
      let s := lexsat_string x_char semicolon_char n_char nv pf in
      let inp := init_input s in
      let n := guess_budget r inp in
      expanded_size r <= 9 * lexsat_size nv pf /\
      length s <= 2 * lexsat_size nv pf /\
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
    intros * WF NEQ; cbv zeta.
    pose proof theRegex_size x_char semicolon_char (lexsat_qbf nv pf) as RS.
    pose proof theString_size x_char semicolon_char n_char (lexsat_qbf nv pf) as SS.
    pose proof size_le_expanded
      (RegexEncoding.theRegex (lexsat_qbf nv pf) x_char semicolon_char) as AST.
    rewrite lexsat_qbf_size in RS, SS.
    split; [exact RS|]; split; [exact SS|].
    split; [|split; [exact (lexsat_regex_frag x_char semicolon_char nv pf)|]].
    { unfold guess_budget, lexsat_regex, lexsat_string.
      replace (remaining_length
                 (init_input (theString (lexsat_qbf nv pf) x_char semicolon_char n_char)) forward)
        with (length (theString (lexsat_qbf nv pf) x_char semicolon_char n_char)) by reflexivity.
      assert ((1 + length (theString (lexsat_qbf nv pf) x_char semicolon_char n_char))
              * regex_size (RegexEncoding.theRegex (lexsat_qbf nv pf) x_char semicolon_char)
              <= (1 + 2 * lexsat_size nv pf) * (9 * lexsat_size nv pf))
        by (apply PeanoNat.Nat.mul_le_mono; lia).
      nia. }
    destruct (lexsat_by_optp x_char semicolon_char _ (lexsat_qbf_wf nv pf WF) pf eq_refl
                ltac:(intros qt IN; eapply repeat_spec, IN) n_char rer NEQ _
                (compute_tr_is_tree _)) as [best JOIN].
    rewrite lexsat_qbf_num_vars in JOIN; eauto.
  Qed.

  Section OptpMembership.
    Context (wr: Patterns.Regex).
    Hypothesis no_early_errors: StaticSemantics.earlyErrors wr [] = Success false.

    Let rer := rer_of wr flags.
    Let lr := linden_of wr.

    Hypothesis lr_nolk: no_lookaround lr.
    Hypothesis lr_nolb: no_lower_bound lr.

    Theorem optp_membership_matcher:
      forall (inp: input),
        let n := guess_budget lr inp in
        n <= S (3 * (1 + remaining_length inp forward) * pattern_size wr) /\
        exists m best,
          Semantics.compilePattern wr rer = Success m /\
          parse_spec rer lr inp n best /\
          length best = S n /\
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

    Theorem optp_membership_e2e:
      forall (s: LWParameters.string),
        let inp := init_input s in
        let n := guess_budget lr inp in
        n <= S (3 * (1 + length s) * pattern_size wr) /\
        exists inst best,
          regExpInitialize wr flags = Success inst /\
          parse_spec rer lr inp n best /\
          length best = S n /\
          exec_agrees inst s (to_MatchState (exec_of_parse rer lr inp best)
                                            (RegExpRecord.capturingGroupsCount rer)).
    Proof.
      intros s inp ?.
      split; [apply (guess_budget_source wr inp)|].
      destruct (optp_membership_poly rer lr inp _ lr_nolk lr_nolb (compute_tr_is_tree _))
        as [best OPTP].
      destruct (matches_regExpExec_result_flags wr lr s no_early_errors eq_refl flags rer
                  eq_refl eq_refl eq_refl) as [inst [INIT RES]]; destruct OPTP as (? & ? & EXECP).
      exists inst, best; unfold linden_result, first_leaf in RES; rewrite EXECP; auto 10.
    Qed.
  End OptpMembership.

End EndToEnd.

Definition end_to_end_results :=
  (@pspace_hardness_matcher, @pspace_hardness_e2e, @pspace_hardness_noneglk_matcher,
   @pspace_hardness_noneglk_e2e, @pspace_membership_matcher, @pspace_membership_e2e,
   @membership_state_size_bound, @optp_hardness_matcher, @optp_hardness_e2e,
   @optp_hardness_machine, @optp_membership_matcher, @optp_membership_e2e).
Print Assumptions end_to_end_results.
