(** * OptP-hardness: CNF LEXICOGRAPHIC SAT reduces to JavaScript regex matching *)

From JsRegexOptp Require Import Basics Qbf GroupMaps GroupMapQbfEquiv Bits RegexEncoding
  HardnessProofs MembershipOptp.
From Linden Require Import Chars Groups Semantics Tree Tactics.
From Linden.Rewriting Require Import ProofSetup FlatMap.
From Warblre Require Import Parameters RegExpRecord Base.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations.

Definition first_of {A} (x y: option A): option A :=
  match x with Some a => Some a | None => y end.

Section OptpHardness.
  Context {params: LindenParameters}.
  Context (q: qbf).
  Hypothesis (WF_q: wf_qbf q).

  Context (x_char semicolon_char n_char: Parameters.Character).
  Context (rer: RegExpRecord).
  Hypothesis (x_semicolon_neq: Character.canonicalize rer x_char <>
    Character.canonicalize rer semicolon_char).

  Hypothesis (ALL_EXISTS: forall qt, List.In qt (fst q) -> qt = Qbf.Exists).

  Local Notation n := (List.length (fst q)).
  Local Notation quants := (fst q).
  Local Notation form := (snd q).
  Local Notation str := (theString q x_char semicolon_char n_char).
  Local Notation ioi := (inp_of_idx q x_char semicolon_char n_char).

  Local Notation with_var i gm := (GroupMap.add i (var_range i) gm).
  Local Notation defvar i := (def_var_regex x_char semicolon_char i).

  Local Notation dvr_spec := (def_var_regex_spec q x_char semicolon_char n_char rer).
  Local Notation cfr_spec :=
    (check_formula_regex_spec q WF_q x_char semicolon_char n_char rer x_semicolon_neq).

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
    destruct form as [pf|pf]; cbn; intro W;
      now rewrite <- (assign_cnf_of_gm n gm pf W), <- (assign_cnf_of_gm n gm' pf W), A.
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
      is_tree rer [Areg (check_formula_regex x_char semicolon_char form)] inp gm forward t ->
      first_gm t gm inp = if gm_satisfies_formula gm form then Some gm else None.
  Proof.
    intros EQ_inp WF TREE.
    pose proof cfr_spec inp gm EQ_inp WF t TREE _ eq_refl as [ALLGM SATIFF].
    unfold first_gm; rewrite first_tree_leaf.
    destruct (tree_leaves t gm inp forward) as [|[inp1 gm1] lvs]; cbn.
    - destruct (gm_satisfies_formula gm form); [elim (proj2 SATIFF eq_refl eq_refl)|easy].
    - rewrite (proj1 SATIFF) by discriminate.
      f_equal; exact (ALLGM (inp1, gm1) (or_introl eq_refl)).
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
    destruct (is_tree_productivity rer [Areg rsub] (ioi (2*i)) (with_var i gm) forward)
      as [tpos TPOS].
    destruct (is_tree_productivity rer [Areg rsub] (ioi (2*i)) gm forward) as [tneg TNEG].
    exists tpos, tneg; do 2 (split; [assumption|]); apply first_gm_app.
    inversion TREE; subst; rewrite app_nil_r in CONT.
    destruct (is_tree_productivity rer [Areg (defvar i)] (ioi (2*(i-1))) gm forward)
      as [tdv TDV].
    pose proof leaves_concat rer (ioi (2*(i-1))) gm forward
      [Areg (defvar i)] [Areg rsub] t tdv CONT TDV as CONCAT.
    rewrite (dvr_spec i _ NZ LE eq_refl tdv gm TDV) in CONCAT.
    eapply FlatMap_pair; eauto using act_from_leaf_determ;
      [apply (afl rer [Areg rsub] forward (ioi (2*i), _) tpos TPOS)
      |apply (afl rer [Areg rsub] forward (ioi (2*i), gm) tneg TNEG)].
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
      intros gm' WF' AG; destruct (WF' i LE) as [E|E]; [left|right]; apply agree_below_S;
        [exact AG | congruence
        |intros j ? ?; rewrite find_add_neq by lia; now apply AG
        |now rewrite find_add_eq, E]. }
    destruct A as [gm|].
    - destruct PA as (WF & SAT & AGR & MAX).
      assert (Si: GroupMap.find i gm = Some (var_range i))
        by (rewrite <- AGR by lia; apply find_add_eq).
      repeat apply conj; [exact WF | exact SAT
        |intros j ? ?; rewrite <- AGR by lia; now rewrite find_add_neq by lia | ].
      intros gm' WF' AGREE LT; apply MAX; auto; apply agree_below_S; auto.
      destruct LT as (j & ? & ? & NONE & SOME & AGRj); assert (j <> i) by congruence.
      assert (i < j) by (destruct (Nat.lt_ge_cases j i);
                           [rewrite AGREE in NONE by lia; congruence | lia]).
      apply AGRj; lia.
    - destruct B as [gm|].
      + destruct PB as (WF & SAT & AGR & MAX).
        repeat apply conj; [exact WF | exact SAT | eauto using agree_below_weaken | ].
        intros gm' WF' AGREE LT; assert (AG: agree_below i gm0 gm')
          by (intros j ? ?; rewrite AGR by lia; now apply AGREE).
        destruct (SPLIT _ WF' AG) as [G|G]; [apply MAX | apply PA]; auto.
        apply agree_below_S; auto; rewrite <- AGR by lia; now rewrite G by lia.
      + intros gm' WF' AGREE; destruct (SPLIT _ WF' AGREE) as [G|G]; [apply PB|apply PA]; auto.
  Qed.

  Theorem theRegex_aux_lexmax i:
      i <> 0 -> i <= n + 1 ->
    forall gm0, wf_gm n gm0 ->
      (forall j, i <= j -> j <= n -> GroupMap.find j gm0 = None) ->
      forall inp qtail t,
        inp = ioi (2*(i-1)) ->
        qtail = List.skipn (i-1) quants ->
        is_tree rer [Areg (theRegex_aux q x_char semicolon_char i qtail)] inp gm0 forward t ->
        lexmax_at i gm0 (first_gm t gm0 inp).
  Proof.
    intros NZ LE gm0 WF0 UNDEF inp qtail t EQ_inp EQ_qtail TREE.
    assert (LEN: i + List.length qtail = n + 1) by (rewrite EQ_qtail, length_skipn; lia).
    pose proof all_exists_skipn (i-1) as ALLQ; rewrite <- EQ_qtail in ALLQ.
    clear LE EQ_qtail; revert i NZ LEN ALLQ gm0 WF0 UNDEF inp t EQ_inp TREE.
    induction qtail as [|qt qtail IH];
      intros i NZ LEN ALLQ gm0 WF0 UNDEF inp t EQ_inp TREE; cbn [List.length] in LEN.
    - assert (i = S n) as -> by lia; replace (S n - 1) with n in EQ_inp by lia.
      rewrite (check_formula_first_gm inp gm0 t EQ_inp WF0 TREE).
      destruct (gm_satisfies_formula gm0 form) eqn:SAT.
      + repeat apply conj; auto using agree_below_refl.
        intros gm' _ AGREE (j & ? & ? & NONE & ? & _); rewrite AGREE in NONE by lia; congruence.
      + intros gm' _ AGREE; now rewrite <- (gm_satisfies_formula_ext gm0 gm').
    - assert (LEn: i <= n) by lia; assert (qt = Qbf.Exists) as -> by (apply ALLQ; now left).
      destruct (def_var_first_gm i inp NZ LEn EQ_inp _ gm0 t TREE)
        as (tpos & tneg & TPOS & TNEG & ->).
      apply lexmax_at_step; [lia | lia | apply UNDEF; lia | idtac | idtac].
      all: apply (IH (S i)); auto using wf_gm_add; try lia;
        [intros; apply ALLQ; now right
        |eauto using undef_gm_add, undef_gm_unchanged | f_equal; lia].
  Qed.

  Theorem theRegex_first_gm_lexmax t:
      is_tree rer [Areg (theRegex q x_char semicolon_char)] (init_input str)
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
    intro TREE.
    pose proof theRegex_aux_lexmax 1 ltac:(lia) ltac:(lia)
      GroupMap.empty (wf_gm_empty n) (fun j _ _ => find_empty j)
      (init_input str) quants t eq_refl eq_refl TREE as SPEC.
    destruct (first_gm t GroupMap.empty (init_input str)) as [gm|];
      [destruct SPEC as (WF & SAT & _ & MAX); repeat apply conj|];
      eauto using agree_below_one.
  Qed.

  Theorem theRegex_first_gm_max t:
      is_tree rer [Areg (theRegex q x_char semicolon_char)] (init_input str)
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
    destruct SPEC as (WF & SAT & MAX); repeat apply conj; auto; intros gm' WF' SAT'.
    destruct (gm_lex_trichotomy n gm' gm WF' WF) as [AGREE | [LT | GT]];
      [rewrite (agree_below_bits n gm' gm AGREE); apply bits_le_refl
      |now apply gm_lex_lt_bits | rewrite MAX in SAT' by assumption; discriminate].
  Qed.

  Theorem reduction_valid pf:
      form = PosForm pf ->
    forall t,
      is_tree rer [Areg (theRegex q x_char semicolon_char)] (init_input str)
              GroupMap.empty forward t ->
      match first_gm t GroupMap.empty (init_input str) with
      | Some gm => is_lex_max_sat n pf (bits_of_gm n gm)
      | None => forall b, length b = n -> assign_cnf b pf = false
      end.
  Proof.
    intros EQ t TREE.
    assert (WFpf: wf_pos_formula n pf) by (pose proof wf_pos_form as W; now rewrite EQ in W).
    pose proof theRegex_first_gm_max t TREE as SPEC.
    destruct (first_gm t GroupMap.empty (init_input str)) as [gm|].
    - destruct SPEC as (WF & SAT & MAX); rewrite EQ in SAT.
      repeat apply conj; [apply bits_of_gm_length | now rewrite assign_cnf_of_gm | ].
      intros b' LEN ?; destruct (bits_of_gm_surj n b' LEN) as [gm' [WF' <-]].
      apply MAX; auto; rewrite EQ; cbn; now rewrite <- (assign_cnf_of_gm n gm' pf WFpf).
    - intros b LEN; destruct (bits_of_gm_surj n b LEN) as [gm' [WF' <-]].
      rewrite assign_cnf_of_gm by assumption; rewrite EQ in SPEC; now apply SPEC.
  Qed.

End OptpHardness.

Section LexSatReduction.
  Context {params: LindenParameters}.
  Context (x_char semicolon_char n_char: Parameters.Character).

  Definition lexsat_qbf (nv: nat) (pf: pos_formula): qbf :=
    (List.repeat Qbf.Exists nv, PosForm pf).

  Definition lexsat_regex (nv: nat) (pf: pos_formula): regex :=
    theRegex (lexsat_qbf nv pf) x_char semicolon_char.

  Definition lexsat_string (nv: nat) (pf: pos_formula): LWParameters.string :=
    theString (lexsat_qbf nv pf) x_char semicolon_char n_char.

  Lemma lexsat_qbf_num_vars nv pf: List.length (fst (lexsat_qbf nv pf)) = nv.
  Proof. apply repeat_length. Qed.

  Definition lexsat_size (nv: nat) (pf: pos_formula): nat :=
    1 + nv + List.length pf + num_literals_pos_formula pf.

  Lemma lexsat_qbf_size nv pf: qbf_size (lexsat_qbf nv pf) = lexsat_size nv pf.
  Proof.
    unfold qbf_size, lexsat_size, lexsat_qbf, num_clauses_qbf, num_clauses_formula,
      num_literals_qbf, num_literals_formula; cbn; now rewrite repeat_length.
  Qed.

  Lemma lexsat_qbf_wf nv pf: wf_pos_formula nv pf -> wf_qbf (lexsat_qbf nv pf).
  Proof. intro; constructor; rewrite repeat_length; now constructor. Qed.

  Context (rer: RegExpRecord).
  Hypothesis (x_semicolon_neq: Character.canonicalize rer x_char <>
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
    intros WF t TREE.
    pose proof reduction_valid (lexsat_qbf nv pf) (lexsat_qbf_wf nv pf WF)
      x_char semicolon_char n_char rer x_semicolon_neq
      ltac:(intros qt IN; eapply repeat_spec, IN) pf eq_refl t TREE as SPEC.
    now rewrite lexsat_qbf_num_vars in SPEC.
  Qed.
End LexSatReduction.

Section Fragment.
  Context {params: LindenParameters}.
  Context (x_char semicolon_char: Parameters.Character).

  Definition in_fragment (r: regex): Prop := no_lookaround r /\ no_lower_bound r.

  Local Ltac frag := unfold in_fragment in *; cbn in *; tauto.

  Lemma def_var_regex_frag v: in_fragment (def_var_regex x_char semicolon_char v).
  Proof. frag. Qed.

  Lemma check_clause_regex_frag c:
    in_fragment (check_clause_regex x_char semicolon_char c).
  Proof.
    unfold check_clause_regex.
    enough (in_fragment (check_clause_regex_aux x_char c)) by frag.
    induction c as [|[] c IH]; frag.
  Qed.

  Lemma check_conjunct_regex_frag cl:
    in_fragment (check_conjunct_regex x_char semicolon_char cl).
  Proof.
    induction cl as [|c cl IH]; [frag|]; pose proof check_clause_regex_frag c; frag.
  Qed.

  Lemma theRegex_aux_frag (q: qbf) pf:
      snd q = PosForm pf ->
    forall ql, (forall qt, List.In qt ql -> qt = Qbf.Exists) ->
    forall v, in_fragment (theRegex_aux q x_char semicolon_char v ql).
  Proof.
    intro EQ; induction ql as [|qt ql IH]; intros ALL v.
    - cbn [theRegex_aux check_formula_regex]; rewrite EQ; apply check_conjunct_regex_frag.
    - assert (qt = Qbf.Exists) as -> by (apply ALL; now left).
      pose proof def_var_regex_frag v.
      pose proof IH ltac:(intros; apply ALL; now right) (S v); frag.
  Qed.

  Theorem theRegex_frag (q: qbf) pf:
      snd q = PosForm pf ->
      (forall qt, List.In qt (fst q) -> qt = Qbf.Exists) ->
      in_fragment (theRegex q x_char semicolon_char).
  Proof. intros EQ ALL; eapply theRegex_aux_frag; eauto. Qed.

  Corollary lexsat_by_optp (q: qbf):
      wf_qbf q ->
    forall pf, snd q = PosForm pf ->
      (forall qt, List.In qt (fst q) -> qt = Qbf.Exists) ->
    forall n_char rer,
      Character.canonicalize rer x_char <> Character.canonicalize rer semicolon_char ->
    forall t,
      is_tree rer [Areg (theRegex q x_char semicolon_char)]
              (init_input (theString q x_char semicolon_char n_char))
              GroupMap.empty forward t ->
      let r := theRegex q x_char semicolon_char in
      let inp := init_input (theString q x_char semicolon_char n_char) in
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
    intros WF_q pf EQ ALL n_char rer NEQ t TREE r inp ?.
    destruct (theRegex_frag q pf EQ ALL) as [NLK NLB].
    destruct (optp_membership_poly rer r inp t NLK NLB TREE) as [best (PARSE & LEN & EXEC)].
    exists best; do 2 (split; [assumption|]); rewrite EXEC.
    now apply (reduction_valid q WF_q x_char semicolon_char n_char rer NEQ ALL pf EQ t TREE).
  Qed.

End Fragment.

Corollary lexsat_regex_frag {params: LindenParameters}
    (x_char semicolon_char: Parameters.Character) nv pf:
    in_fragment (lexsat_regex x_char semicolon_char nv pf).
Proof.
  unfold lexsat_regex; eapply theRegex_frag; [reflexivity | intros qt IN; eapply repeat_spec, IN].
Qed.
