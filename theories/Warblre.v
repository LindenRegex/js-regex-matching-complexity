From JsRegexOptp Require Import Qbf RegexEncoding GroupMaps HardnessProofs MembershipProof
  WarblreExtensions WarblreEncoding LindenExtensions.
From JsRegexOptp Require Import Basics.
From JsRegexOptp Require RegexEncodingPoslk HardnessPoslk.
From Linden Require Import LWParameters Chars Groups Semantics Tree RegexpTranslation
  FunctionalUtils ResultTranslation EquivMain.
From Warblre Require Import Patterns StaticSemantics Result Base EarlyErrors
  Parameters RegExpRecord Semantics Frontend Notation.
From Stdlib Require Import List Lia PeanoNat ZArith.
Import ListNotations.

Definition linden_of {params: LindenParameters} (wr: Patterns.Regex): regex :=
  warblre_to_linden' wr 0 (buildnm wr).

Section TranslationSize.
  Context {params: LindenParameters}.

  Lemma atomesc_size:
    forall ae nm lr, atomesc_to_linden ae nm = Success lr -> regex_size lr = 1.
  Proof.
    intros [] nm lr TR; cbn in TR; try (injection TR as <-; reflexivity).
    destruct (nameidx nm _); [injection TR as <- | discriminate]; reflexivity.
  Qed.

  Lemma quantpref_size:
    forall qp quant, wquantpref_to_linden qp = Success quant ->
      forall greedy lr, regex_size (quant greedy lr) = 1 + regex_size lr.
  Proof.
    intros [] quant TR; cbn in TR; try (injection TR as <-; reflexivity).
    destruct (_ <=? _); [injection TR as <- | discriminate]; reflexivity.
  Qed.

  Lemma warblre_to_linden_size (wr: Patterns.Regex):
    forall n nm lr,
      warblre_to_linden wr n nm = Success lr -> regex_size lr <= pattern_size wr.
  Proof.
    induction wr; intros n nm lr TR; cbn in TR |- *; unfold Result.bind in TR;
      repeat (match type of TR with
              | context [ match ?e with _ => _ end ] => destruct e eqn:?
              end; cbn in TR; unfold Result.bind in TR); try discriminate.
    all: repeat match goal with
         | H: atomesc_to_linden _ _ = Success _ |- _ => apply atomesc_size in H
         | H: warblre_to_linden _ _ _ = Success _ |- _ =>
             first [apply IHwr in H | apply IHwr1 in H | apply IHwr2 in H]
         | H: wquantpref_to_linden _ = Success _ |- _ =>
             pose proof (quantpref_size _ _ H); clear H
         end.
    all: try injection TR as <-; cbn in *;
         repeat match goal with
         | H: forall _ _, regex_size (?quant _ _) = _ |- context [?quant] => rewrite H
         end; lia.
  Qed.

  Corollary linden_of_size wr: regex_size (linden_of wr) <= pattern_size wr.
  Proof.
    unfold linden_of, warblre_to_linden'.
    destruct (warblre_to_linden wr 0 (buildnm wr)) eqn:TR;
      [eapply warblre_to_linden_size, TR | cbn; apply pattern_size_pos].
  Qed.

  Corollary guess_budget_source wr inp:
      guess_budget (linden_of wr) inp
      <= S (3 * (1 + remaining_length inp forward) * pattern_size wr).
  Proof. unfold guess_budget; pose proof linden_of_size wr; nia. Qed.

  Corollary fuel_budget_source wr inp:
      no_lower_bound (linden_of wr) ->
      fuel_budget (linden_of wr) inp
      <= S (3 * (1 + length (input_str inp)) * pattern_size wr * S (3 * pattern_size wr)).
  Proof.
    intro NLB; unfold fuel_budget.
    pose proof expanded_size_nolb _ NLB; pose proof linden_of_size wr; nia.
  Qed.
End TranslationSize.

Section TranslationFragment.
  Context {params: LindenParameters}.

  Lemma quantpref_shape:
    forall qp quant, wquantpref_to_linden qp = Success quant ->
      exists min delta,
        (forall greedy lr, quant greedy lr = Quantified greedy min delta lr) /\
        (min = 0 -> quantprefix_no_lower_bound qp).
  Proof.
    intros [] quant TR; cbn in TR; try destruct (_ <=? _); inversion TR; do 2 eexists; easy.
  Qed.

  Lemma warblre_to_linden_fragment (wr: Patterns.Regex):
    forall n nm lr,
      warblre_to_linden wr n nm = Success lr ->
      (no_lookaround lr -> pattern_no_lookaround wr) /\
      (no_neg_lookaround lr -> pattern_no_neg_lookaround wr) /\
      (no_lower_bound lr -> pattern_no_lower_bound wr).
  Proof.
    induction wr; intros n nm lr TR; cbn in TR |- *;
      repeat match type of TR with
             | context [ Result.bind ?e _ ] => destruct e eqn:?; cbn in TR
             | context [ match ?e with _ => _ end ] => destruct e eqn:?; cbn in TR
             end; try discriminate; try injection TR as <-.
    all: repeat match goal with
         | H: wquantpref_to_linden _ = Success _ |- _ =>
             destruct (quantpref_shape _ _ H) as (? & ? & -> & ?); clear H
         | H: warblre_to_linden _ _ _ = Success _ |- _ =>
             first [apply IHwr in H | apply IHwr1 in H | apply IHwr2 in H]
         end; cbn in *; intuition discriminate.
  Qed.

  Corollary warblre_to_linden_no_lookaround (wr: Patterns.Regex) n nm lr:
      warblre_to_linden wr n nm = Success lr ->
      no_lookaround lr -> pattern_no_lookaround wr.
  Proof. intros TR%warblre_to_linden_fragment; apply TR. Qed.

  Corollary warblre_to_linden_no_neg_lookaround (wr: Patterns.Regex) n nm lr:
      warblre_to_linden wr n nm = Success lr ->
      no_neg_lookaround lr -> pattern_no_neg_lookaround wr.
  Proof. intros TR%warblre_to_linden_fragment; apply TR. Qed.

  Corollary warblre_to_linden_no_lower_bound (wr: Patterns.Regex) n nm lr:
      warblre_to_linden wr n nm = Success lr ->
      no_lower_bound lr -> pattern_no_lower_bound wr.
  Proof. intros TR%warblre_to_linden_fragment; apply TR. Qed.
End TranslationFragment.

Section StickyExec.
  Context {params: LindenParameters}.

  #[export] Instance linden_StringLaws: StringLaws.
  Proof.
    assert (ID: forall (s: LWParameters.string) i, char_pos s i = i) by (induction i; cbn; auto).
    split; cbn; intros; rewrite ?ID; auto.
  Qed.
End StickyExec.

Section WarblreBits.
  Context {params: LindenParameters}.

  Lemma defined_bits_to_MatchState nv inp gm ms:
      wf_gm nv gm ->
      to_MatchState (Some (inp, gm)) nv = Some ms ->
      defined_bits (Notation.MatchState.captures ms) = bits_of_gm nv gm.
  Proof.
    intros WF [= <-]; cbn [Notation.MatchState.captures].
    unfold defined_bits, bits_of_gm, gm_satisfies_var; rewrite <- seq_shift, !map_map.
    apply map_ext_in; intros i I%in_seq; edestruct (WF (S i)) as [->| ->]; (lia || reflexivity).
  Qed.
End WarblreBits.

Lemma linden_result_tree {params: LindenParameters} {rer r inp t}:
    is_tree rer [Areg r] inp GroupMap.empty forward t ->
    linden_result rer r inp = first_leaf t inp.
Proof. intro T; unfold linden_result; cbv zeta; now rewrite (is_tree_eq_compute_tr _ T). Qed.

Lemma linden_result_matches_at {params: LindenParameters} {rer r inp}:
    linden_result rer r inp <> None <-> matches_at rer r inp.
Proof. symmetry; apply matches_at_compute_tr. Qed.

Section MatchesTransport.
  Context {params: LindenParameters}.
  Context (wr: Patterns.Regex) (lr: regex) (str: LWParameters.string).
  Hypothesis EE: StaticSemantics.earlyErrors wr [] = Success false.
  Hypothesis WL: lr = linden_of wr.

  Lemma wr_equiv_lr: equiv_regex wr lr.
  Proof. rewrite WL; apply earlyErrors_pass_translation_nomonad, EE. Qed.

  Lemma to_MatchState_some res n: to_MatchState res n <> None <-> res <> None.
  Proof. destruct res as [[]|]; simpl; split; congruence. Qed.

  Section AnyRecord.
    Context (rer: RegExpRecord).
    Hypothesis CAPS: RegExpRecord.capturingGroupsCount rer =
      StaticSemantics.countLeftCapturingParensWithin wr nil.

    Lemma warblre_result:
      EquivMain.compilePattern wr rer str 0 =
        to_MatchState (linden_result rer lr (init_input str))
                      (RegExpRecord.capturingGroupsCount rer).
    Proof. auto using equiv_main_reconstruct_str0. Qed.

    Lemma matcher_shape:
      exists m res,
        Semantics.compilePattern wr rer = Success m /\
        m str 0 = Success res /\
        EquivMain.compilePattern wr rer str 0 = res.
    Proof.
      pose proof equiv_main_str0 wr lr rer str wr_equiv_lr CAPS
        (EarlyErrors.earlyErrors _ EE) as [m [res [COMP [EXEC _]]]].
      exists m, res; unfold EquivMain.compilePattern; rewrite COMP, EXEC; auto.
    Qed.

    Lemma matcher_result:
      exists m,
        Semantics.compilePattern wr rer = Success m /\
        m str 0 = Success (to_MatchState (linden_result rer lr (init_input str))
                             (RegExpRecord.capturingGroupsCount rer)).
    Proof.
      destruct matcher_shape as [m [res (COMP & EXEC & RES)]].
      exists m; rewrite EXEC, <- RES, warblre_result; auto.
    Qed.

    Lemma compiled_shape flags:
        rer = rer_of wr flags ->
        exists m res,
          Semantics.compilePattern wr rer = Success m /\
          regExpInitialize wr flags = Success (reg_exp_instance wr flags rer m 0%Z) /\
          m str 0 = Success res /\
          EquivMain.compilePattern wr rer str 0 = res.
    Proof.
      intro Heqrer; destruct matcher_shape as [m [res (COMP & EXEC & RES)]].
      exists m, res; auto using exec_initialize.
    Qed.

    Corollary matches_regExpExec_result flags:
        RegExpFlags.y flags = true ->
        rer = rer_of wr flags ->
        exists inst,
          regExpInitialize wr flags = Success inst /\
          exec_agrees inst str (EquivMain.compilePattern wr rer str 0).
    Proof.
      intros STICKY Heqrer; destruct matcher_shape as [m [res (COMP & EXEC & RES)]]; rewrite RES.
      eexists; split; [eauto using exec_initialize|].
      eauto using exec_sticky, EarlyErrors.earlyErrors, linden_StringLaws.
    Qed.

    Context (b: bool).
    Hypothesis MATCHES: matches_at rer lr (init_input str) <-> b = true.

    Theorem matches_warblre: EquivMain.compilePattern wr rer str 0 <> None <-> b = true.
    Proof.
      rewrite warblre_result, <- MATCHES, <- linden_result_matches_at.
      apply to_MatchState_some.
    Qed.

    Theorem matches_matcher:
      exists m res,
        Semantics.compilePattern wr rer = Success m /\
        m str 0 = Success res /\
        (res <> None <-> b = true).
    Proof.
      destruct matcher_shape as [m [res (COMP & EXEC & RES)]].
      exists m, res; rewrite <- RES in EXEC |- *; auto using matches_warblre.
    Qed.

    Lemma matches_shape flags:
        rer = rer_of wr flags ->
        exists m res,
          regExpInitialize wr flags = Success (reg_exp_instance wr flags rer m 0%Z) /\
          m str 0 = Success res /\
          (res <> None <-> b = true).
    Proof.
      intros [m [res (_ & I & E & RES)]]%(compiled_shape flags).
      exists m, res; rewrite <- RES in E |- *; auto using matches_warblre.
    Qed.

    Corollary matches_regExpInitialize flags:
        rer = rer_of wr flags ->
        exists inst res,
          regExpInitialize wr flags = Success inst /\
          RegExpInstance.regExpMatcher inst str 0 = Success res /\
          (res <> None <-> b = true).
    Proof. intros [m [res H]]%(matches_shape flags); do 2 eexists; exact H. Qed.

    Corollary matches_regExpExec flags:
        RegExpFlags.y flags = true ->
        rer = rer_of wr flags ->
        exists inst,
          regExpInitialize wr flags = Success inst /\
          ((exists inst', regExpExec inst str = Success (Null inst')) <-> b = false).
    Proof.
      intros STICKY [inst [INIT RES]]%(matches_regExpExec_result flags STICKY); exists inst.
      destruct (exec_null_exotic _ _ _ RES) as [-> _]; eauto using none_iff_false, matches_warblre.
    Qed.

    Corollary matches_regExpExec_exotic flags:
        RegExpFlags.y flags = true ->
        rer = rer_of wr flags ->
        exists inst,
          regExpInitialize wr flags = Success inst /\
          ((exists A inst', regExpExec inst str = Success (Exotic A inst')) <-> b = true).
    Proof.
      intros STICKY [inst [INIT RES]]%(matches_regExpExec_result flags STICKY); exists inst.
      destruct (exec_null_exotic _ _ _ RES) as [_ ->]; eauto using matches_warblre.
    Qed.

  End AnyRecord.

  Corollary matches_regExpExec_result_flags flags rer:
      RegExpFlags.y flags = true ->
      rer = rer_of wr flags ->
      exists inst,
        regExpInitialize wr flags = Success inst /\
        exec_agrees inst str (to_MatchState (linden_result rer lr (init_input str))
                                            (RegExpRecord.capturingGroupsCount rer)).
  Proof.
    intros STICKY Heqrer; pose proof (f_equal RegExpRecord.capturingGroupsCount Heqrer) as CAPS.
    rewrite <- (warblre_result rer CAPS); eauto using matches_regExpExec_result.
  Qed.
End MatchesTransport.

Section MembershipTransport.
  Context {params: LindenParameters}.
  Context (wr: Patterns.Regex) (rer: RegExpRecord).
  Hypothesis EE: StaticSemantics.earlyErrors wr [] = Success false.
  Hypothesis CAPS: RegExpRecord.capturingGroupsCount rer
                   = StaticSemantics.countLeftCapturingParensWithin wr nil.

  Let lr := linden_of wr.

  Lemma matcher_at_input:
    exists m,
      Semantics.compilePattern wr rer = Success m /\
      forall inp,
        m (input_str inp) (idx inp)
        = Success (to_MatchState (linden_result rer lr inp)
                                 (RegExpRecord.capturingGroupsCount rer)).
  Proof.
    pose proof (fun inp => equiv_main wr lr rer inp (earlyErrors_pass_translation_nomonad wr EE)
                  CAPS (EarlyErrors.earlyErrors wr EE)) as EM.
    destruct (EM (init_input [])) as [m [_ (COMP & _)]]; exists m; split; [exact COMP|].
    intro inp; destruct (EM inp) as [? [res (COMP' & EXEC & _)]]; rewrite COMP in COMP'.
    injection COMP' as <-; generalize (equiv_main_reconstruct wr lr rer inp CAPS EE eq_refl).
    unfold EquivMain.compilePattern; rewrite COMP, EXEC; now intros ->.
  Qed.

  Lemma fuel_budget_spec (r: regex) inp:
      fuel_budget r inp > MembershipProof.actions_fuel inp [Areg r] forward.
  Proof.
    pose proof MembershipProof.poly_fuel inp r; pose proof remaining_le_full_length inp forward.
    unfold fuel_budget; nia.
  Qed.

  Lemma compute_result_poly inp:
      res_to_leaf (compute_result rer [Areg lr] inp GroupMap.empty forward (fuel_budget lr inp))
      = Some (linden_result rer lr inp).
  Proof.
    unfold linden_result; eapply compute_result_spec;
      eauto using afr_refl, fuel_budget_spec, compute_tr_is_tree.
  Qed.
End MembershipTransport.

Definition regex_test {params: LindenParameters}
    (wr: Patterns.Regex) (flags: RegExpFlags) (s: LWParameters.string) (b: bool): Prop :=
  exists inst res,
    regExpInitialize wr flags = Success inst /\
    RegExpInstance.regExpMatcher inst s 0 = Success res /\
    (res <> None <-> b = true) /\
    ((exists inst', regExpExec inst s = Success (Null inst')) <-> b = false) /\
    ((exists A inst', regExpExec inst s = Success (Exotic A inst')) <-> b = true).

Section FrontendJoin.
  Context {params: LindenParameters}.
  Context (wr: Patterns.Regex) (flags: RegExpFlags) (str: LWParameters.string) (b: bool).

  Lemma frontend_all:
    (exists inst res,
        regExpInitialize wr flags = Success inst /\
        RegExpInstance.regExpMatcher inst str 0 = Success res /\
        (res <> None <-> b = true)) ->
    (exists inst,
        regExpInitialize wr flags = Success inst /\
        ((exists inst', regExpExec inst str = Success (Null inst')) <-> b = false)) ->
    (exists inst,
        regExpInitialize wr flags = Success inst /\
        ((exists A inst', regExpExec inst str = Success (Exotic A inst')) <-> b = true)) ->
    regex_test wr flags str b.
  Proof.
    intros [inst [res (INIT & MATCH & IFF)]] [? (INIT' & NULL)] [? (INIT'' & EXOTIC)].
    rewrite INIT in *; injection INIT' as <-; injection INIT'' as <-; exists inst, res; auto.
  Qed.
End FrontendJoin.

Section WarblreHardness.
  Context {params: LindenParameters}.
  Context (q: qbf).
  Hypothesis WF_q: wf_qbf q.
  Context (a_char semicolon_char z_char: Parameters.Character).

  Let wr := theRegex_w q a_char semicolon_char.
  Let lr := theRegex q a_char semicolon_char.
  Let str := theString q a_char semicolon_char z_char.

  Lemma wr_earlyErrors: StaticSemantics.earlyErrors wr [] = Success false.
  Proof. apply regex_encoding_w_earlyErrors, WF_q. Qed.

  Lemma wr_to_linden: lr = linden_of wr.
  Proof. unfold lr, wr, linden_of, warblre_to_linden'; now rewrite regex_encoding_wl. Qed.

  Lemma wr_nolb: no_lower_bound (linden_of wr).
  Proof. rewrite <- wr_to_linden; apply theRegex_nolb. Qed.

  Theorem theRegex_w_nolb: pattern_no_lower_bound wr.
  Proof. eauto using warblre_to_linden_no_lower_bound, regex_encoding_wl, theRegex_nolb. Qed.

  Local Hint Resolve wr_earlyErrors wr_to_linden : core.

  Section AnyRecord.
    Context (rer: RegExpRecord).
    Hypothesis a_semicolon_neq: Character.canonicalize rer a_char <>
      Character.canonicalize rer semicolon_char.
    Hypothesis CAPS: RegExpRecord.capturingGroupsCount rer =
      StaticSemantics.countLeftCapturingParensWithin wr nil.

    Lemma qbf_matches: matches_at rer lr (init_input str) <-> qbf_true q = true.
    Proof. apply qbf_regex; assumption. Qed.

    Local Hint Resolve qbf_matches : core.

    Theorem qbf_regex_warblre_matcher:
      exists m res,
        Semantics.compilePattern wr rer = Success m /\
        m str 0 = Success res /\
        (res <> None <-> qbf_true q = true).
    Proof. apply matches_matcher with (lr := lr); auto. Qed.

  End AnyRecord.

  Section FromFlags.
    Context (flags: RegExpFlags).

    Let rer := rer_of wr flags.

    Hypothesis a_semicolon_neq: Character.canonicalize rer a_char <>
      Character.canonicalize rer semicolon_char.

    Local Ltac flags_transport L := apply L with (lr := lr) (rer := rer); auto using qbf_matches.

    Theorem qbf_regex_warblre_frontend:
      exists inst res,
        regExpInitialize wr flags = Success inst /\
        RegExpInstance.regExpMatcher inst str 0 = Success res /\
        (res <> None <-> qbf_true q = true).
    Proof. flags_transport matches_regExpInitialize. Qed.

    Theorem qbf_regex_warblre_frontend_exec:
      RegExpFlags.y flags = true ->
      exists inst,
        regExpInitialize wr flags = Success inst /\
        ((exists inst', regExpExec inst str = Success (Null inst')) <-> qbf_true q = false).
    Proof. intro; flags_transport matches_regExpExec. Qed.

    Theorem qbf_regex_warblre_frontend_exotic:
      RegExpFlags.y flags = true ->
      exists inst,
        regExpInitialize wr flags = Success inst /\
        ((exists A inst', regExpExec inst str = Success (Exotic A inst')) <->
         qbf_true q = true).
    Proof. intros; flags_transport matches_regExpExec_exotic. Qed.

    Theorem qbf_regex_warblre_frontend_all:
      RegExpFlags.y flags = true ->
      regex_test wr flags str (qbf_true q).
    Proof.
      intros; apply frontend_all;
        eauto using qbf_regex_warblre_frontend, qbf_regex_warblre_frontend_exec,
                    qbf_regex_warblre_frontend_exotic.
    Qed.
  End FromFlags.

End WarblreHardness.

Section WarblreHardnessPoslk.
  Context {params: LindenParameters}.
  Context (q: qbf).
  Hypothesis WF_q: wf_qbf q.
  Context (a_char semicolon_char z_char: Parameters.Character).

  Let wr := theRegex_poslk_w q a_char semicolon_char z_char.
  Let lr := RegexEncodingPoslk.theRegex a_char semicolon_char z_char q.
  Let str := theString q a_char semicolon_char z_char.

  Lemma wr_poslk_earlyErrors: StaticSemantics.earlyErrors wr [] = Success false.
  Proof. apply regex_encoding_poslk_w_earlyErrors, WF_q. Qed.

  Lemma wr_poslk_to_linden: lr = linden_of wr.
  Proof. unfold lr, wr, linden_of, warblre_to_linden'; now rewrite regex_encoding_poslk_wl. Qed.

  Lemma wr_poslk_nolb: no_lower_bound (linden_of wr).
  Proof. rewrite <- wr_poslk_to_linden; apply RegexEncodingPoslk.theRegex_poslk_nolb. Qed.

  Lemma wr_poslk_noneglk: no_neg_lookaround (linden_of wr).
  Proof. rewrite <- wr_poslk_to_linden; apply RegexEncodingPoslk.theRegex_poslk_noneglk. Qed.

  Theorem theRegex_poslk_w_noneglk: pattern_no_neg_lookaround wr.
  Proof.
    eauto using warblre_to_linden_no_neg_lookaround, regex_encoding_poslk_wl,
                RegexEncodingPoslk.theRegex_poslk_noneglk.
  Qed.

  Theorem theRegex_poslk_w_nolb: pattern_no_lower_bound wr.
  Proof.
    eauto using warblre_to_linden_no_lower_bound, regex_encoding_poslk_wl,
                RegexEncodingPoslk.theRegex_poslk_nolb.
  Qed.

  Local Hint Resolve wr_poslk_earlyErrors wr_poslk_to_linden : core.

  Section AnyRecord.
    Context (rer: RegExpRecord).
    Hypothesis a_semicolon_neq: Character.canonicalize rer a_char <>
      Character.canonicalize rer semicolon_char.
    Hypothesis a_z_neq: Character.canonicalize rer a_char <>
      Character.canonicalize rer z_char.
    Hypothesis z_not_lineterminator: ~In z_char Character.line_terminators.
    Hypothesis a_not_lineterminator: ~In a_char Character.line_terminators.
    Hypothesis CAPS: RegExpRecord.capturingGroupsCount rer =
      StaticSemantics.countLeftCapturingParensWithin wr nil.

    Lemma qbf_poslk_matches: matches_at rer lr (init_input str) <-> qbf_true q = true.
    Proof. apply HardnessPoslk.qbf_regex; assumption. Qed.

    Local Hint Resolve qbf_poslk_matches : core.

    Theorem qbf_poslk_warblre_matcher:
      exists m res,
        Semantics.compilePattern wr rer = Success m /\
        m str 0 = Success res /\
        (res <> None <-> qbf_true q = true).
    Proof. apply matches_matcher with (lr := lr); auto. Qed.
  End AnyRecord.

  Section FromFlags.
    Context (flags: RegExpFlags).
    Hypothesis z_not_lineterminator: ~In z_char Character.line_terminators.
    Hypothesis a_not_lineterminator: ~In a_char Character.line_terminators.

    Let rer := rer_of wr flags.

    Hypothesis a_semicolon_neq: Character.canonicalize rer a_char <>
      Character.canonicalize rer semicolon_char.
    Hypothesis a_z_neq: Character.canonicalize rer a_char <>
      Character.canonicalize rer z_char.

    Local Ltac poslk_transport L :=
      apply L with (lr := lr) (rer := rer); auto using qbf_poslk_matches.

    Theorem qbf_poslk_warblre_frontend:
      exists inst res,
        regExpInitialize wr flags = Success inst /\
        RegExpInstance.regExpMatcher inst str 0 = Success res /\
        (res <> None <-> qbf_true q = true).
    Proof. poslk_transport matches_regExpInitialize. Qed.

    Theorem qbf_poslk_warblre_frontend_exec:
      RegExpFlags.y flags = true ->
      exists inst,
        regExpInitialize wr flags = Success inst /\
        ((exists inst', regExpExec inst str = Success (Null inst')) <-> qbf_true q = false).
    Proof. intro; poslk_transport matches_regExpExec. Qed.

    Theorem qbf_poslk_warblre_frontend_exotic:
      RegExpFlags.y flags = true ->
      exists inst,
        regExpInitialize wr flags = Success inst /\
        ((exists A inst', regExpExec inst str = Success (Exotic A inst')) <->
         qbf_true q = true).
    Proof. intros; poslk_transport matches_regExpExec_exotic. Qed.

    Theorem qbf_poslk_warblre_frontend_all:
      RegExpFlags.y flags = true ->
      regex_test wr flags str (qbf_true q).
    Proof.
      intros; apply frontend_all;
        eauto using qbf_poslk_warblre_frontend, qbf_poslk_warblre_frontend_exec,
                    qbf_poslk_warblre_frontend_exotic.
    Qed.
  End FromFlags.

End WarblreHardnessPoslk.
