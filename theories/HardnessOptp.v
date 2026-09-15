(** * OptP-hardness: CNF LEXICOGRAPHIC SAT reduces to JavaScript regex matching *)

From JsRegexOptp Require Import Basics Qbf GroupMaps Bits RegexEncoding
  HardnessProofs MembershipOptp WarblreExtensions WarblreEncoding Warblre.
From Linden Require Import Chars Groups Semantics Tree LWParameters
  ResultTranslation EquivMain.
From Linden.Rewriting Require Import ProofSetup.
From Warblre Require Import Parameters RegExpRecord Base Notation StaticSemantics
  Result Frontend.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations.

Definition first_of {A} (x y: option A): option A :=
  match x with Some a => Some a | None => y end.

Section OptpHardness.
  Context {params: LindenParameters}.
  Context (q: qbf).
  Hypothesis (WF_q: wf_qbf q).

  Context (a_char semicolon_char z_char: Parameters.Character).
  Context (rer: RegExpRecord).
  Hypothesis (a_semicolon_neq: Character.canonicalize rer a_char <>
    Character.canonicalize rer semicolon_char).

  Hypothesis (ALL_EXISTS: forall qt, List.In qt (fst q) -> qt = Qbf.Exists).

  Local Notation n := (List.length (fst q)).
  Local Notation quants := (fst q).
  Local Notation form := (snd q).
  Local Notation str := (theString q a_char semicolon_char z_char).
  Local Notation ioi := (inp_of_idx q a_char semicolon_char z_char).

  Local Notation with_var i gm := (GroupMap.add i (var_range i) gm).
  Local Notation defvar i := (def_var_regex a_char semicolon_char i).

  Local Notation dvr_spec := (def_var_regex_spec q a_char semicolon_char z_char rer).
  Local Notation cfr_spec :=
    (check_formula_regex_spec q WF_q a_char semicolon_char z_char rer a_semicolon_neq).

  Lemma all_exists_skipn k qt: List.In qt (List.skipn k quants) -> qt = Qbf.Exists.
  Proof.
    intro IN; apply ALL_EXISTS; now rewrite <- (firstn_skipn k quants), in_app_iff; right.
  Qed.

  Lemma wf_pos_form: wf_pos_formula n (inner_pos_formula form).
  Proof. destruct q as [ql f]; cbn; inversion WF_q as [? ? W]; now inversion W. Qed.

  Lemma gm_satisfies_formula_ext gm gm':
      agree_below (S n) gm gm' ->
      gm_satisfies_formula gm form = gm_satisfies_formula gm' form.
  Proof.
    intros A%(agree_below_bits n); pose proof wf_pos_form as W; revert W.
    destruct form as [pf|pf]; cbn; intro W; now rewrite <- !(assign_cnf_of_gm n _ pf W), A.
  Qed.

  Definition first_gm (t: tree) (gm: group_map) (inp: input): option group_map :=
    option_map snd (tree_res t gm inp forward).

  Remark first_gm_first_leaf t inp:
    first_gm t GroupMap.empty inp = option_map snd (first_leaf t inp).
  Proof. reflexivity. Qed.

  Lemma first_gm_app t gm inp t1 gm1 inp1 t2 gm2 inp2:
      tree_leaves t gm inp forward =
        tree_leaves t1 gm1 inp1 forward ++ tree_leaves t2 gm2 inp2 forward ->
      first_gm t gm inp = first_of (first_gm t1 gm1 inp1) (first_gm t2 gm2 inp2).
  Proof.
    intro E; unfold first_gm, first_of; rewrite !first_tree_leaf, E, hd_error_app.
    now destruct (hd_error (tree_leaves t1 gm1 inp1 forward)).
  Qed.

  Lemma check_formula_first_gm inp gm t:
      inp = ioi (2*n) -> wf_gm n gm ->
      is_tree rer [Areg (check_formula_regex a_char semicolon_char form)] inp gm forward t ->
      first_gm t gm inp = if gm_satisfies_formula gm form then Some gm else None.
  Proof.
    intros EQ_inp WF TREE; unfold first_gm; rewrite first_tree_leaf.
    pose proof cfr_spec inp gm EQ_inp WF t TREE _ eq_refl as [ALLGM [NE SAT]].
    destruct (tree_leaves t gm inp forward) as [|[inp1 gm1] lvs]; cbn.
    - destruct (gm_satisfies_formula gm form); [destruct (SAT eq_refl eq_refl) | easy].
    - rewrite NE by discriminate; f_equal; apply (ALLGM (inp1, gm1)); now left.
  Qed.

  Lemma def_var_first_gm i inp:
      i <> 0 -> i <= n -> inp = ioi (2*(i-1)) ->
    forall rsub gm t,
      is_tree rer [Areg (Sequence (defvar i) rsub)] inp gm forward t ->
      exists tpos tneg,
        is_tree rer [Areg rsub] (ioi (2*i)) (with_var i gm) forward tpos /\
        is_tree rer [Areg rsub] (ioi (2*i)) gm forward tneg /\
        first_gm t gm inp = first_of (first_gm tpos (with_var i gm) (ioi (2*i)))
                                     (first_gm tneg gm (ioi (2*i))).
  Proof.
    intros NZ LE ? rsub gm t TREE.
    destruct (is_tree_productivity rer [Areg rsub] (ioi (2*i)) (with_var i gm) forward) as [tpos TPOS],
             (is_tree_productivity rer [Areg rsub] (ioi (2*i)) gm forward) as [tneg TNEG].
    exists tpos, tneg; repeat split; eauto; apply first_gm_app.
    inversion TREE; subst; rewrite app_nil_r in CONT.
    pose proof leaves_concat _ _ _ _ [Areg (defvar i)] [Areg rsub] _ _ CONT (compute_tr_is_tree rer)
      as CONCAT.
    rewrite (dvr_spec i _ NZ LE eq_refl _ gm (compute_tr_is_tree rer)) in CONCAT.
    eauto using FlatMap_pair, act_from_leaf_determ, afl.
  Qed.

  Definition lexmax_at (i: nat) (gm0: group_map) (res: option group_map): Prop :=
    match res with
    | Some gm =>
        wf_gm n gm /\
        gm_satisfies_formula gm form = true /\
        agree_below i gm0 gm /\
        (forall gm', wf_gm n gm' -> agree_below i gm gm' -> gm_lex_lt n gm gm' ->
           gm_satisfies_formula gm' form = false)
    | None =>
        forall gm', wf_gm n gm' -> agree_below i gm0 gm' ->
          gm_satisfies_formula gm' form = false
    end.

  Lemma lexmax_at_step i gm0:
      i <> 0 -> i <= n -> GroupMap.find i gm0 = None ->
    forall A B,
      lexmax_at (S i) (with_var i gm0) A -> lexmax_at (S i) gm0 B ->
      lexmax_at i gm0 (first_of A B).
  Proof.
    intros ? LE ? A B PA PB.
    assert (SPLIT: forall gm', wf_gm n gm' -> agree_below i gm0 gm' ->
              agree_below (S i) gm0 gm' \/ agree_below (S i) (with_var i gm0) gm'). {
      intros gm' WF' AG; destruct (WF' i LE) as [E|E]; [left|right]; apply agree_below_S; auto.
      - congruence.
      - intros j ? ?; now rewrite find_add_neq, AG by lia.
      - now rewrite find_add_eq, E. }
    destruct A as [gm|].
    - destruct PA as (WF & SAT & AGR & MAX).
      repeat split; auto; [intros j ? ?; now rewrite <- AGR, find_add_neq by lia | ].
      intros gm' WF' AGREE LT; apply MAX; auto; apply agree_below_S; auto.
      destruct LT as (j & ? & ? & NONE & SOME & AGRj), (Nat.lt_trichotomy i j) as [? | [-> | ?]];
        [apply AGRj; lia | rewrite <- AGR, find_add_eq in NONE by lia; discriminate
        | rewrite AGREE in NONE by lia; congruence].
    - destruct B as [gm|].
      + destruct PB as (WF & SAT & AGR & MAX).
        repeat split; eauto using agree_below_weaken.
        intros gm' WF' AGREE LT; assert (AG: agree_below i gm0 gm')
          by (intros j ? ?; rewrite AGR by lia; now apply AGREE).
        destruct (SPLIT _ WF' AG) as [G|G]; [apply MAX | apply PA]; auto.
        apply agree_below_S; auto; now rewrite <- AGR, G by lia.
      + intros gm' WF' AGREE; destruct (SPLIT _ WF' AGREE) as [G|G]; [apply PB|apply PA]; auto.
  Qed.

  Theorem theRegex_aux_lexmax i:
      i <> 0 -> i <= n + 1 ->
    forall gm0, wf_gm n gm0 ->
      (forall j, i <= j -> j <= n -> GroupMap.find j gm0 = None) ->
      forall inp qtail t,
        inp = ioi (2*(i-1)) ->
        qtail = List.skipn (i-1) quants ->
        is_tree rer [Areg (theRegex_aux q a_char semicolon_char i qtail)] inp gm0 forward t ->
        lexmax_at i gm0 (first_gm t gm0 inp).
  Proof.
    intros NZ LE gm0 WF0 UNDEF inp qtail t EQ_inp EQ_qtail TREE.
    assert (LEN: i + List.length qtail = n + 1) by (rewrite EQ_qtail, length_skipn; lia).
    pose proof all_exists_skipn (i-1) as ALLQ; rewrite <- EQ_qtail in ALLQ; clear LE EQ_qtail.
    induction qtail as [|qt qtail IH]
      in i, NZ, LEN, ALLQ, gm0, WF0, UNDEF, inp, t, EQ_inp, TREE |- *; cbn [List.length] in LEN.
    - assert (i = S n) as -> by lia; replace (S n - 1) with n in EQ_inp by lia.
      rewrite check_formula_first_gm by auto; destruct (gm_satisfies_formula gm0 form) eqn:SAT.
      + repeat split; auto using agree_below_refl.
        intros gm' _ AGREE (j & ? & ? & NONE & ? & _); rewrite AGREE in NONE by lia; congruence.
      + intros gm' _ ?%gm_satisfies_formula_ext; congruence.
    - assert (LEn: i <= n) by lia; assert (qt = Qbf.Exists) as -> by (apply ALLQ; now left).
      destruct (def_var_first_gm i inp NZ LEn EQ_inp _ gm0 t TREE)
        as (tpos & tneg & TPOS & TNEG & ->).
      apply lexmax_at_step; try lia; [apply UNDEF; lia | ..].
      all: apply (IH (S i)); auto using wf_gm_add, in_cons; try lia;
        [eauto using undef_gm_add, undef_gm_unchanged | f_equal; lia].
  Qed.

  Theorem theRegex_first_gm_lexmax t:
      is_tree rer [Areg (theRegex q a_char semicolon_char)] (init_input str)
              GroupMap.empty forward t ->
      match first_gm t GroupMap.empty (init_input str) with
      | Some gm =>
          wf_gm n gm /\ gm_satisfies_formula gm form = true /\
          (forall gm', wf_gm n gm' -> gm_lex_lt n gm gm' ->
             gm_satisfies_formula gm' form = false)
      | None =>
          forall gm', wf_gm n gm' -> gm_satisfies_formula gm' form = false
      end.
  Proof.
    intros SPEC%(theRegex_aux_lexmax 1); auto using wf_gm_empty, find_empty; try lia.
    destruct (first_gm t GroupMap.empty (init_input str)) as [gm|];
      [destruct SPEC as (WF & SAT & _ & MAX)|]; eauto using agree_below_one.
  Qed.

  Theorem theRegex_first_gm_max t:
      is_tree rer [Areg (theRegex q a_char semicolon_char)] (init_input str)
              GroupMap.empty forward t ->
      match first_gm t GroupMap.empty (init_input str) with
      | Some gm =>
          wf_gm n gm /\ gm_satisfies_formula gm form = true /\
          (forall gm', wf_gm n gm' -> gm_satisfies_formula gm' form = true ->
             bits_le (bits_of_gm n gm') (bits_of_gm n gm) = true)
      | None => forall gm', wf_gm n gm' -> gm_satisfies_formula gm' form = false
      end.
  Proof.
    intro TREE; pose proof theRegex_first_gm_lexmax t TREE as SPEC.
    destruct (first_gm t GroupMap.empty (init_input str)) as [gm|]; auto.
    destruct SPEC as (WF & SAT & MAX); repeat split; auto; intros gm' WF' SAT'.
    destruct (gm_lex_trichotomy n gm' gm WF' WF) as [->%(agree_below_bits n) | [LT | GT]];
      auto using bits_le_refl, gm_lex_lt_bits; now rewrite MAX in SAT'.
  Qed.

  Theorem reduction_valid pf:
      form = PosForm pf ->
    forall t,
      is_tree rer [Areg (theRegex q a_char semicolon_char)] (init_input str)
              GroupMap.empty forward t ->
      match first_gm t GroupMap.empty (init_input str) with
      | Some gm => is_lex_max_sat n pf (bits_of_gm n gm)
      | None => forall b, length b = n -> assign_cnf b pf = false
      end.
  Proof.
    intros EQ t TREE; pose proof wf_pos_form as WFpf; rewrite EQ in WFpf.
    pose proof theRegex_first_gm_max t TREE as SPEC; rewrite EQ in SPEC.
    destruct (first_gm t GroupMap.empty (init_input str)) as [gm|].
    - destruct SPEC as (WF & SAT & MAX).
      repeat split; auto using bits_of_gm_length; [now rewrite assign_cnf_of_gm | ].
      intros b' LEN SAT'; destruct (bits_of_gm_surj n b' LEN) as [gm' [WF' <-]].
      rewrite assign_cnf_of_gm in SAT' by assumption; auto.
    - intros b LEN; destruct (bits_of_gm_surj n b LEN) as [gm' [WF' <-]].
      rewrite assign_cnf_of_gm by assumption; now apply SPEC.
  Qed.

End OptpHardness.

Section LexSatReduction.
  Context {params: LindenParameters}.
  Context (a_char semicolon_char z_char: Parameters.Character).

  Definition lexsat_qbf (nv: nat) (pf: pos_formula): qbf :=
    (List.repeat Qbf.Exists nv, PosForm pf).

  Definition lexsat_regex (nv: nat) (pf: pos_formula): regex :=
    theRegex (lexsat_qbf nv pf) a_char semicolon_char.

  Definition lexsat_string (nv: nat) (pf: pos_formula): LWParameters.string :=
    theString (lexsat_qbf nv pf) a_char semicolon_char z_char.

  Lemma lexsat_qbf_num_vars nv pf: List.length (fst (lexsat_qbf nv pf)) = nv.
  Proof. apply repeat_length. Qed.

  Lemma lexsat_qbf_all_exists nv pf qt: List.In qt (fst (lexsat_qbf nv pf)) -> qt = Qbf.Exists.
  Proof. apply repeat_spec. Qed.

  Definition lexsat_size (nv: nat) (pf: pos_formula): nat :=
    1 + nv + List.length pf + num_literals_pos_formula pf.

  Lemma lexsat_qbf_size nv pf: qbf_size (lexsat_qbf nv pf) = lexsat_size nv pf.
  Proof.
    unfold qbf_size, lexsat_size; cbn; now rewrite repeat_length.
  Qed.

  Lemma lexsat_qbf_wf nv pf: wf_pos_formula nv pf -> wf_qbf (lexsat_qbf nv pf).
  Proof. intro; constructor; rewrite repeat_length; now constructor. Qed.

  Context (rer: RegExpRecord).
  Hypothesis (a_semicolon_neq: Character.canonicalize rer a_char <>
    Character.canonicalize rer semicolon_char).

  Theorem lexsat_reduction nv pf:
      wf_pos_formula nv pf ->
    forall t,
      is_tree rer [Areg (lexsat_regex nv pf)] (init_input (lexsat_string nv pf))
              GroupMap.empty forward t ->
      match option_map snd (first_leaf t (init_input (lexsat_string nv pf))) with
      | Some gm => is_lex_max_sat nv pf (bits_of_gm nv gm)
      | None => forall b, List.length b = nv -> assign_cnf b pf = false
      end.
  Proof.
    intros WF t TREE; eapply reduction_valid with (pf := pf) in TREE as SPEC;
      eauto using lexsat_qbf_wf, lexsat_qbf_all_exists.
    now rewrite lexsat_qbf_num_vars in SPEC.
  Qed.
End LexSatReduction.

Section Fragment.
  Context {params: LindenParameters}.
  Context (a_char semicolon_char: Parameters.Character).

  Definition in_fragment (r: regex): Prop := no_lookaround r /\ no_lower_bound r.

  Local Ltac frag := unfold in_fragment in *; cbn in *; tauto.

  Lemma def_var_regex_frag v: in_fragment (def_var_regex a_char semicolon_char v).
  Proof. frag. Qed.

  Lemma check_clause_regex_frag c:
    in_fragment (check_clause_regex a_char semicolon_char c).
  Proof.
    unfold check_clause_regex; enough (in_fragment (check_clause_regex_aux a_char c)) by frag.
    induction c as [|[] c IH]; frag.
  Qed.

  Lemma check_conjunct_regex_frag cl:
    in_fragment (check_conjunct_regex a_char semicolon_char cl).
  Proof.
    induction cl as [|c cl IH]; [frag|]; pose proof check_clause_regex_frag c; frag.
  Qed.

  Lemma theRegex_aux_frag (q: qbf) pf:
      snd q = PosForm pf ->
    forall ql, (forall qt, List.In qt ql -> qt = Qbf.Exists) ->
    forall v, in_fragment (theRegex_aux q a_char semicolon_char v ql).
  Proof.
    intro EQ; induction ql as [|qt ql IH]; intros ALL v.
    - cbn [theRegex_aux check_formula_regex]; rewrite EQ; apply check_conjunct_regex_frag.
    - assert (qt = Qbf.Exists) as -> by (apply ALL; now left).
      pose proof def_var_regex_frag v; pose proof IH ltac:(auto using in_cons) (S v); frag.
  Qed.

  Theorem theRegex_frag (q: qbf) pf:
      snd q = PosForm pf ->
      (forall qt, List.In qt (fst q) -> qt = Qbf.Exists) ->
      in_fragment (theRegex q a_char semicolon_char).
  Proof. intros EQ ALL; eauto using theRegex_aux_frag. Qed.

  Theorem theRegex_w_nolk (q: qbf):
      wf_qbf q ->
    forall pf, snd q = PosForm pf ->
      (forall qt, List.In qt (fst q) -> qt = Qbf.Exists) ->
      pattern_no_lookaround (theRegex_w q a_char semicolon_char).
  Proof.
    intros; eapply warblre_to_linden_no_lookaround, theRegex_frag; eauto using regex_encoding_wl.
  Qed.

  Corollary lexsat_by_optp (q: qbf):
      wf_qbf q ->
    forall pf, snd q = PosForm pf ->
      (forall qt, List.In qt (fst q) -> qt = Qbf.Exists) ->
    forall z_char rer,
      Character.canonicalize rer a_char <> Character.canonicalize rer semicolon_char ->
    forall t,
      is_tree rer [Areg (theRegex q a_char semicolon_char)]
              (init_input (theString q a_char semicolon_char z_char))
              GroupMap.empty forward t ->
      let r := theRegex q a_char semicolon_char in
      let inp := init_input (theString q a_char semicolon_char z_char) in
      let nb := guess_budget r inp in
      exists best,
        parse_spec rer r inp nb best /\
        length best = S nb /\
        match option_map snd (exec_of_parse rer r inp best) with
        | Some gm =>
            is_lex_max_sat (List.length (fst q)) pf (bits_of_gm (List.length (fst q)) gm)
        | None => forall b, List.length b = List.length (fst q) -> assign_cnf b pf = false
        end.
  Proof.
    intros WF_q pf EQ ALL z_char rer NEQ t TREE r inp ?.
    destruct (theRegex_frag q pf EQ ALL) as [NLK NLB].
    destruct (optp_membership_poly rer r inp t NLK NLB TREE) as [best (PARSE & LEN & EXEC)].
    exists best; do 2 (split; [assumption|]); rewrite EXEC; eapply reduction_valid; eassumption.
  Qed.

End Fragment.

Corollary lexsat_regex_frag {params: LindenParameters}
    (a_char semicolon_char: Parameters.Character) nv pf:
    in_fragment (lexsat_regex a_char semicolon_char nv pf).
Proof. eapply theRegex_frag, lexsat_qbf_all_exists; reflexivity. Qed.

Section LexSatWarblre.
  Context {params: LindenParameters}.
  Context (a_char semicolon_char: Parameters.Character) (nv: nat) (pf: pos_formula).
  Hypothesis WF: wf_pos_formula nv pf.

  Let wr := theRegex_w (lexsat_qbf nv pf) a_char semicolon_char.

  Lemma lexsat_w_earlyErrors: StaticSemantics.earlyErrors wr [] = Success false.
  Proof. apply wr_earlyErrors, lexsat_qbf_wf, WF. Qed.

  Lemma lexsat_w_to_linden:
    lexsat_regex a_char semicolon_char nv pf = linden_of wr.
  Proof. apply wr_to_linden, lexsat_qbf_wf, WF. Qed.

  Lemma lexsat_w_frag: in_fragment (linden_of wr).
  Proof. rewrite <- lexsat_w_to_linden; apply lexsat_regex_frag. Qed.

  Lemma lexsat_w_nolk: pattern_no_lookaround wr.
  Proof. apply theRegex_w_nolk with (pf := pf); eauto using lexsat_qbf_wf, lexsat_qbf_all_exists. Qed.

  Lemma lexsat_w_nolb: pattern_no_lower_bound wr.
  Proof. apply theRegex_w_nolb, lexsat_qbf_wf, WF. Qed.

  Lemma lexsat_ngroups (rer: RegExpRecord):
      RegExpRecord.capturingGroupsCount rer
      = StaticSemantics.countLeftCapturingParensWithin wr [] ->
      RegExpRecord.capturingGroupsCount rer = nv.
  Proof.
    intros ->; unfold wr; rewrite theRegex_w_ngroups; auto using lexsat_qbf_wf, lexsat_qbf_num_vars.
  Qed.

  Context (z_char: Parameters.Character).
  Let s := lexsat_string a_char semicolon_char z_char nv pf.

  Lemma lexsat_w_matcher (rer: RegExpRecord):
      RegExpRecord.capturingGroupsCount rer
      = StaticSemantics.countLeftCapturingParensWithin wr [] ->
      exists m,
        Warblre.spec.Semantics.Semantics.compilePattern wr rer = Success m /\
        m s 0 = Success (to_MatchState (linden_result rer
                           (lexsat_regex a_char semicolon_char nv pf) (init_input s)) nv).
  Proof.
    intro CAPS; destruct (matcher_result _ _ s lexsat_w_earlyErrors lexsat_w_to_linden
                            rer CAPS) as [m (COMP & EXEC)].
    exists m; rewrite (lexsat_ngroups rer CAPS) in EXEC; auto.
  Qed.

  Lemma lexsat_w_exec_result (flags: RegExpFlags) (rer: RegExpRecord):
      RegExpFlags.y flags = true ->
      rer = rer_of wr flags ->
      exists inst,
        regExpInitialize wr flags = Success inst /\
        exec_agrees inst s
          (to_MatchState (linden_result rer (lexsat_regex a_char semicolon_char nv pf)
                            (init_input s)) (RegExpRecord.capturingGroupsCount rer)).
  Proof.
    intros; eapply matches_regExpExec_result_flags;
      auto using lexsat_w_earlyErrors, lexsat_w_to_linden.
  Qed.
End LexSatWarblre.

Lemma lexsat_answer {params: LindenParameters}
    (a_char semicolon_char z_char: Parameters.Character) (rer: RegExpRecord) nv pf:
    wf_pos_formula nv pf ->
    Character.canonicalize rer a_char <> Character.canonicalize rer semicolon_char ->
    let q := lexsat_qbf nv pf in
    match to_MatchState (linden_result rer (RegexEncoding.theRegex q a_char semicolon_char)
                           (init_input (theString q a_char semicolon_char z_char))) nv with
    | Some ms => is_lex_max_sat nv pf (defined_bits (Notation.MatchState.captures ms))
    | None => forall b, length b = nv -> assign_cnf b pf = false
    end.
Proof.
  intros WF NEQ; cbv zeta; unfold linden_result; set (t := compute_tr _ _ _ _ _).
  pose proof (compute_tr_is_tree rer : is_tree _ _ _ _ _ t) as TREE.
  pose proof lexsat_reduction a_char semicolon_char z_char rer NEQ nv pf WF t TREE as RED.
  pose proof theRegex_first_gm_max (lexsat_qbf nv pf) (lexsat_qbf_wf nv pf WF) a_char semicolon_char
    z_char rer NEQ (lexsat_qbf_all_exists nv pf) t TREE as WFGM.
  rewrite lexsat_qbf_num_vars, first_gm_first_leaf in WFGM; unfold lexsat_string in RED.
  destruct (first_leaf t _) as [[inp gm]|]; cbn [option_map snd] in RED, WFGM; [|exact RED].
  now rewrite <- (defined_bits_to_MatchState nv inp gm _ (proj1 WFGM) eq_refl) in RED.
Qed.

Corollary lexsat_answer_flags {params: LindenParameters}
    (a_char semicolon_char z_char: Parameters.Character)
    (flags: RegExpFlags) (rer: RegExpRecord) nv pf:
    wf_pos_formula nv pf ->
    Character.canonicalize rer a_char <> Character.canonicalize rer semicolon_char ->
    let q := lexsat_qbf nv pf in
    rer = rer_of (theRegex_w q a_char semicolon_char) flags ->
    match to_MatchState (linden_result rer (RegexEncoding.theRegex q a_char semicolon_char)
                           (init_input (theString q a_char semicolon_char z_char)))
                        (RegExpRecord.capturingGroupsCount rer) with
    | Some ms => is_lex_max_sat nv pf (defined_bits (Notation.MatchState.captures ms))
    | None => forall b, length b = nv -> assign_cnf b pf = false
    end.
Proof.
  intros WF ? ? RER; rewrite (lexsat_ngroups _ _ _ _ WF rer ltac:(now rewrite RER)).
  now apply lexsat_answer.
Qed.
