From Linden Require Import Regex Chars Parameters Groups Tree Semantics Tactics
  FunctionalUtils Equivalence.
From JsRegexOptp Require Import Qbf RegexEncoding RegexEncodingPoslk GroupMaps
  HardnessProofs.
From Warblre Require Import RegExpRecord Parameters Base.
Require Import List Lia.
Import ListNotations.

Section HardnessPoslk.
  Context {params: LindenParameters}.
  Context (x_char semicolon_char n_char: Parameters.Character).
  Context (rer: RegExpRecord).
  Context (q: qbf).
  Hypothesis (WF_q: wf_qbf q).

  Hypothesis (x_semicolon_neq: Character.canonicalize rer x_char <>
    Character.canonicalize rer semicolon_char).
  Hypothesis (x_n_neq: Character.canonicalize rer x_char <>
    Character.canonicalize rer n_char).
  Hypothesis (semicolon_n_neq: Character.canonicalize rer semicolon_char <>
    Character.canonicalize rer n_char).
  Hypothesis (n_not_lineterminator: ~In n_char Character.line_terminators).
  Hypothesis (x_not_lineterminator: ~In x_char Character.line_terminators).

  Let str := theString q x_char semicolon_char n_char.
  Let quants := fst q.
  Let clauses := snd q.
  Let n := length quants.

  (* Definition inp_of_idx (i: nat) :=
    Input (List.skipn i str) (List.rev (List.firstn i str)). *)
  Definition inp_of_idx (i: nat) := inp_of_idx q x_char semicolon_char n_char i.

  Definition wf_gm_n_i (strlen: nat) (gm: group_map) (i: nat): Prop :=
    GroupMap.find i gm = None \/
    GroupMap.find i gm = Some (GroupMap.Range (strlen - 1) (Some strlen)).

  Definition wf_gm_n (strlen: nat) (gm: group_map): Prop :=
    forall i, i >= S n -> wf_gm_n_i strlen gm i.

  Definition wf_gm_poslk (strlen: nat) (gm: group_map): Prop :=
    wf_gm q gm /\ wf_gm_n strlen gm.

  Lemma char_match_diff:
    forall a b, Character.canonicalize rer a <> Character.canonicalize rer b ->
      char_match rer a (CdSingle b) = false.
  Proof.
    intros a b NEQ. unfold char_match. simpl. apply FunctionalUtils.EqDec_neqb. auto.
  Qed.

  Lemma char_match_refl:
    forall c, char_match rer c (CdSingle c) = true.
  Proof.
    intro c. unfold char_match. simpl. apply EqDec.reflb.
  Qed.

  Lemma read_char_refl:
    forall c next pref,
      read_char rer (CdSingle c) (Input (c::next) pref) forward =
        Some (c, Input next (c::pref)).
  Proof.
    intros c next pref. unfold read_char. rewrite char_match_refl. reflexivity.
  Qed.

  (* TODO Move to Linden *)
  Lemma gm_add_close_open:
    forall startIdx endIdx, startIdx <= endIdx ->
      forall gm gid, GroupMap.close endIdx gid (GroupMap.open startIdx gid gm) =
        GroupMap.add gid (GroupMap.Range startIdx (Some endIdx)) gm.
  Proof.
  Admitted.

  Lemma ss_xsemicolon:
    forall k pref, StrictSuffix.strict_suffix
      (Input (concat (repeat [x_char; semicolon_char] k) ++ [n_char]) (semicolon_char :: x_char :: pref))
      (Input (x_char :: semicolon_char :: concat (repeat [x_char; semicolon_char] k) ++ [n_char]) pref)
      forward.
  Proof.
    intros k pref. apply StrictSuffix.ss_next with (inp2 := Input (semicolon_char :: concat (repeat [x_char; semicolon_char] k) ++ [n_char]) (x_char :: pref)).
    - simpl. reflexivity.
    - constructor. reflexivity.
  Qed.

  Lemma capture_n_regex_spec:
    forall gid k inp pref,
      inp = Input ((List.concat (List.repeat [x_char; semicolon_char] k)) ++ [n_char]) pref ->
      forall gm t, is_tree rer [Areg (capture_n_regex x_char semicolon_char n_char gid)] inp gm forward t ->
        tree_leaves t gm inp forward =
          [(Input [] (n_char :: List.concat (List.repeat [semicolon_char; x_char] k) ++ pref),
            GroupMap.add gid (GroupMap.Range (length (input_str inp) - 1) (Some (length (input_str inp)))) gm)].
  Proof.
    intros gid k. induction k.
    - simpl. intros inp pref -> gm t TREE.
      unfold capture_n_regex in TREE.
      inversion TREE. subst r1 r2 cont inp gm0 dir t0.
      simpl in CONT.
      inversion CONT. subst t greedy r1 cont inp gm0 dir tquant gidl.
      assert (plus = +∞). {
        destruct plus; try discriminate; auto.
      }
      subst plus. clear H1. simpl in *.
      (* titer has no leaves *)
      inversion ISTREE1. subst r1 r2 cont inp gm0 dir t. simpl in CONT0.
      inversion CONT0.
      1: { exfalso. simpl in READ. rewrite char_match_diff in READ; auto. discriminate. }
      subst cd cont inp gm0 dir titer. simpl.
      clear CONT0 READ ISTREE1 CONT TREE.
      inversion SKIP. subst gid0 r1 cont inp gm0 dir tskip.
      inversion TREECONT.
      2: { exfalso. simpl in READ. rewrite char_match_refl in READ. discriminate. }
      subst cd cont inp gm0 dir treecont. rewrite read_char_refl in READ.
      injection READ as <- <-.
      inversion TREECONT0. subst gid0 cont inp gm0 dir tcont.
      inversion TREECONT1. subst inp gm0 dir treecont.
      simpl. unfold advance_input'. simpl.
      f_equal. f_equal.
      rewrite app_length, rev_length. simpl.
      replace (length pref + 1 - 1) with (length pref) by lia. rewrite PeanoNat.Nat.add_comm.
      simpl. apply gm_add_close_open. lia.
    - simpl. intros inp pref -> gm t TREE.
      unfold capture_n_regex in TREE.
      inversion TREE. subst r1 r2 cont inp gm0 dir t0. clear TREE. simpl in CONT.
      unfold x_semicolon_star in CONT.
      inversion CONT. subst greedy r1 cont inp gm0 dir t tquant gidl. clear CONT.
      assert (plus = +∞). {
        destruct plus; try discriminate; auto.
      }
      subst plus. clear H1.
      (* tskip has no leaf *)
      inversion SKIP. subst gid0 r1 cont inp gm0 dir tskip. clear SKIP.
      inversion TREECONT.
      1: { exfalso. unfold read_char in READ. rewrite char_match_diff in READ; auto. discriminate. }
      subst cd cont inp gm0 dir treecont. simpl. rewrite app_nil_r. clear TREECONT.
      inversion ISTREE1. subst r1 r2 cont inp gm0 dir t. clear ISTREE1. simpl in CONT.
      inversion CONT; rewrite read_char_refl in READ0; try discriminate.
      injection READ0 as <- <-. subst cd cont inp gm0 dir titer. clear CONT.
      inversion TREECONT; rewrite read_char_refl in READ0; try discriminate.
      injection READ0 as <- <-. subst cd cont inp gm0 dir tcont. clear TREECONT.
      inversion TREECONT0. 2: { exfalso. apply CHECKFAIL, ss_xsemicolon. } 
      subst strcheck cont inp gm0 dir tcont0. clear TREECONT0.
      assert (TREECONT': is_tree rer [Areg (capture_n_regex x_char semicolon_char n_char gid)] (Input (concat (repeat [x_char; semicolon_char] k) ++ [n_char]) (semicolon_char :: x_char :: pref)) gm forward treecont). {
        assert (exists treecont', is_tree rer [Areg (capture_n_regex x_char semicolon_char n_char gid)] (Input (concat (repeat [x_char; semicolon_char] k) ++ [n_char]) (semicolon_char :: x_char :: pref)) gm forward treecont'). {
          eexists. apply FunctionalUtils.compute_tr_is_tree.
        }
        destruct H as [treecont' H].
        unfold capture_n_regex in H.
        inversion H. subst r1 r2 cont t inp gm0 dir.
        simpl in CONT.
        assert (treecont' = treecont). {
          eapply is_tree_determ; eauto.
        }
        subst treecont'. auto.
      }
      specialize (IHk _ (semicolon_char :: x_char :: pref) eq_refl _ _ TREECONT').
      simpl. unfold advance_input'. simpl.
      rewrite IHk.
      f_equal. f_equal.
      + admit.
      + f_equal. f_equal.
        * simpl. admit.
        * f_equal. simpl. admit.
  Admitted.

  Lemma substr_last:
    forall pref, substr (Input [n_char] pref) (length (rev pref ++ [n_char]) - 1) (length (rev pref ++ [n_char])) = [n_char].
  Proof.
    intro pref. unfold substr. simpl.
    assert (length (rev pref ++ [n_char]) >= 1). {
      rewrite app_length. simpl. lia.
    }
    replace (length (rev pref ++ [n_char]) - (length (rev pref ++ [n_char]) - 1)) with 1 by lia.
    rewrite app_length. simpl. replace (length (rev pref) + 1 - 1) with (length (rev pref)) by lia.
    rewrite skipn_app, skipn_all, PeanoNat.Nat.sub_diag. simpl. reflexivity.
  Qed.

  Lemma read_backref_n_succ:
    forall gm gid pref,
      GroupMap.find gid gm = Some (GroupMap.Range (length (input_str (Input [n_char] pref)) - 1) (Some (length (input_str (Input [n_char] pref))))) ->
      read_backref rer gm gid (Input [n_char] pref) forward = Some ([n_char], Input [] (n_char :: pref)).
  Proof.
    intros gm gid pref SOME.
    unfold read_backref. rewrite SOME. simpl.
    assert (length (rev pref ++ [n_char]) >= 1). {
      rewrite app_length. simpl. lia.
    }
    replace (length (rev pref ++ [n_char]) - (length (rev pref ++ [n_char]) - 1)) with 1 by lia.
    simpl. rewrite substr_last. simpl. rewrite EqDec.reflb. reflexivity.
  Qed.

  Lemma read_backref_None:
    forall gm gid inp dir,
      GroupMap.find gid gm = None ->
      read_backref rer gm gid inp dir = Some ([], inp).
  Proof.
    intros gm gid inp dir NONE. unfold read_backref. rewrite NONE. reflexivity.
  Qed.

  Lemma anchor_satisfied_EndInput_notend:
    forall c next pref, ~In c Character.line_terminators ->
      anchor_satisfied rer EndInput (Input (c::next) pref) = false.
  Proof.
    intros c next pref NOT_LINETERM. unfold anchor_satisfied. simpl.
    replace (Utils.List.inb c Character.line_terminators) with false. 2: {
      symmetry. apply Bool.not_true_is_false. rewrite Utils.List.inb_spec. auto.
    }
    apply Bool.andb_false_r.
  Qed.

  Lemma substr_last':
    forall next pref l,
      l = length (rev pref ++ next ++ [n_char]) ->
      substr (Input (next ++ [n_char]) pref) (l-1) l = [n_char].
  Proof.
  Admitted.

  Lemma read_backref_n_notend:
    forall gm gid len inp k pref,
      inp = Input (x_char :: semicolon_char :: concat (repeat [x_char; semicolon_char] k) ++ [n_char]) pref ->
      len = length (input_str inp) ->
      GroupMap.find gid gm = Some (GroupMap.Range (len-1) (Some len)) ->
      read_backref rer gm gid inp forward = None.
  Proof.
    intros gm gid len inp k pref -> -> SOME.
    unfold read_backref. rewrite SOME.
    simpl.
    set (l := length (rev pref ++ x_char :: semicolon_char :: _ ++ [n_char])).
    assert (l >= 1). {
      unfold l. rewrite app_length. simpl. lia.
    }
    replace (l - (l - 1)) with 1 by lia. simpl.
    do 2 rewrite app_comm_cons.
    rewrite substr_last'. 2: { do 2 rewrite <- app_comm_cons. auto. }
    simpl. rewrite FunctionalUtils.EqDec_neqb; auto.
    intro ABS. inversion ABS. contradiction.
  Qed.


  Lemma check_n_before_end:
    forall gm gid k inp pref,
      gid >= S n -> wf_gm_n (length (input_str (Input (concat (repeat [x_char; semicolon_char] (S k)) ++ [n_char]) pref))) gm ->
      inp = (Input (x_char :: semicolon_char :: concat (repeat [x_char; semicolon_char] k) ++ [n_char]) pref) ->
      forall t, is_tree rer [Areg (Backreference gid); Areg (Anchor EndInput)] inp gm forward t ->
        tree_leaves t gm inp forward = [].
  Proof.
    intros gm gid k inp pref VALID_gid WF_gm -> t TREE.
    unfold wf_gm_n in WF_gm. specialize (WF_gm gid VALID_gid). destruct WF_gm as [NONE | SOME].
    - inversion TREE; rewrite read_backref_None in READ_BACKREF by auto; try discriminate.
      injection READ_BACKREF as <- <-. subst gid0 cont inp gm0 dir t. clear TREE.
      inversion TREECONT; rewrite anchor_satisfied_EndInput_notend in ANCHOR by auto; try discriminate.
      subst a cont inp gm0 dir tcont. simpl. reflexivity.
    - inversion TREE; erewrite read_backref_n_notend in READ_BACKREF by eauto; try discriminate.
      simpl. reflexivity.
  Qed.

  Lemma check_n_regex_spec:
    forall gid k inp pref,
      gid >= S n ->
      inp = Input ((List.concat (List.repeat [x_char; semicolon_char] k)) ++ [n_char]) pref ->
      forall gm, wf_gm_n_i (length (input_str inp)) gm gid ->
        forall t, is_tree rer [Areg (check_n_regex x_char semicolon_char gid)] inp gm forward t ->
          (tree_leaves t gm inp forward <> [] <-> GroupMap.find gid gm = Some (GroupMap.Range (length (input_str inp) - 1) (Some (length (input_str inp))))) /\
          (forall lf, In lf (tree_leaves t gm inp forward) ->
            lf = (Input [] (n_char :: List.concat (List.repeat [semicolon_char; x_char] k) ++ pref), gm)).
  Proof.
    intros gid k. induction k.
    - simpl. intros inp pref VALID_gid -> gm WF_gm t TREE.
      unfold wf_gm_n in WF_gm.
      destruct WF_gm as [NONE | SOME].
      + (* Prove False <-> False *)
        replace (tree_leaves t gm (Input [n_char] pref) forward) with (nil (A := leaf)).
        2: {
          symmetry.
          unfold check_n_regex in TREE.
          inversion TREE. subst r1 r2 cont inp gm0 dir t0. simpl in CONT. clear TREE.
          inversion CONT. subst r1 r2 cont inp gm0 dir t0. simpl in CONT0. clear CONT.
          unfold x_semicolon_star in CONT0. inversion CONT0. subst gidl t greedy r1 cont inp gm0 dir tquant. clear CONT0.
          assert (plus = +∞). {
            destruct plus; try discriminate; auto.
          }
          subst plus. clear H1.
          (* titer has no leaves *)
          inversion ISTREE1. subst r1 r2 cont inp gm0 dir t. clear ISTREE1.
          simpl in CONT. inversion CONT. 1: { exfalso. unfold read_char in READ. rewrite char_match_diff in READ by auto. discriminate. }
          subst cd cont inp gm0 dir titer. clear READ CONT.
          (* tcont has no leaves either *)
          inversion SKIP; unfold read_backref in READ_BACKREF; rewrite NONE in READ_BACKREF; try discriminate.
          subst gid0 cont inp gm0 dir tskip. injection READ_BACKREF as <- <-. clear SKIP.
          inversion TREECONT.
          1: { exfalso. unfold anchor_satisfied in ANCHOR. destruct (RegExpRecord.multiline rer); simpl in ANCHOR; try discriminate.
          rewrite Utils.List.inb_spec in ANCHOR. contradiction. }
          simpl. reflexivity.
        }
        split.
        * split; try congruence.
        * intros lf H. inversion H.
      + (* Prove True <-> True *)
        unfold check_n_regex, x_semicolon_star in TREE.
        inversion TREE. subst r1 r2 cont inp gm0 dir t0. simpl in CONT. clear TREE.
        inversion CONT. subst r1 r2 cont inp gm0 dir t0. simpl in CONT0. clear CONT.
        inversion CONT0. subst gidl t greedy r1 cont inp gm0 dir tquant.
        assert (plus = +∞). { destruct plus; try discriminate; auto. }
        subst plus. clear H1 CONT0.
        (* titer has no leaves *)
        inversion ISTREE1. subst r1 r2 cont inp gm0 dir t. clear ISTREE1.
        simpl in CONT. inversion CONT. 1: { exfalso. unfold read_char in READ. rewrite char_match_diff in READ by auto. discriminate. }
        subst cd cont inp gm0 dir titer. clear READ CONT.
        (* tskip has a leaf *)
        inversion SKIP; rewrite read_backref_n_succ in READ_BACKREF by auto; try discriminate.
        injection READ_BACKREF as <- <-. subst gid0 cont inp gm0 dir tskip. clear SKIP.
        inversion TREECONT. 2: { unfold anchor_satisfied in ANCHOR. simpl in ANCHOR. discriminate. }
        subst a cont inp gm0 dir tcont. clear TREECONT ANCHOR.
        inversion TREECONT0. subst inp gm0 dir treecont.
        simpl.
        split.
        * split; auto. discriminate.
        * intros lf []; try contradiction. congruence. 
    - intros inp pref VALID_gid -> gm WF_gm t TREE. unfold check_n_regex, x_semicolon_star in TREE. simpl in TREE.
      (* Reduce to IHk *)
      inversion TREE. subst r1 r2 cont inp gm0 dir t0. clear TREE.
      inversion CONT. subst r1 r2 cont inp gm0 dir t0. clear CONT. simpl in CONT0.
      inversion CONT0. subst gidl t greedy r1 cont inp gm0 dir tquant. clear CONT0.
      assert (plus = +∞). { destruct plus; try discriminate; auto. } subst plus. clear H1.
      inversion ISTREE1. subst r1 r2 cont inp gm0 dir t. clear ISTREE1. simpl in CONT.
      inversion CONT; rewrite read_char_refl in READ; try discriminate.
      injection READ as <- <-. subst cd cont inp gm0 dir titer. clear CONT.
      inversion TREECONT; rewrite read_char_refl in READ; try discriminate.
      injection READ as <- <-. subst cd cont inp gm0 dir tcont. clear TREECONT.
      inversion TREECONT0. 2: { exfalso. apply CHECKFAIL, ss_xsemicolon. }
      subst strcheck cont inp gm0 dir tcont0. clear PROGRESS TREECONT0.
      specialize (IHk _ (semicolon_char :: x_char :: pref) VALID_gid eq_refl gm).
      specialize_prove IHk. {
        simpl. simpl in WF_gm. do 2 rewrite <- app_assoc. simpl. auto.
      }
      specialize (IHk treecont).
      specialize_prove IHk. {
        assert (exists t', is_tree rer [Areg (check_n_regex x_char semicolon_char gid)]
        (Input (concat (repeat [x_char; semicolon_char] k) ++
        [n_char]) (semicolon_char :: x_char :: pref)) gm
        forward t'). { eexists. apply FunctionalUtils.compute_tr_is_tree. }
        destruct H as [t' TREE'].
        unfold check_n_regex in TREE'.
        inversion TREE'. subst r1 r2 cont inp gm0 dir t.
        simpl in CONT. inversion CONT. subst r1 r2 cont inp gm0 dir t. simpl in CONT0.
        unfold x_semicolon_star in CONT0.
        assert (treecont = t'). { eapply is_tree_determ; eauto. }
        subst t'. auto.
      }
      (* tskip is empty *)
      apply check_n_before_end with (k := k) (pref := pref) in SKIP; auto.
      simpl. rewrite SKIP. rewrite app_nil_r.
      unfold advance_input'. simpl.
      destruct IHk as [IHk1 IHk2]. rewrite IHk1.
      split.
      + simpl. do 2 rewrite <- app_assoc. simpl. reflexivity.
      + intros lf IN_lf. specialize (IHk2 lf IN_lf). rewrite IHk2.
        f_equal. f_equal. admit.
  Admitted.

  Lemma wf_gm_poslk_add:
    forall gm, wf_gm_poslk (length str) gm ->
      forall i, i <= n ->
        wf_gm_poslk (length str)
          (GroupMap.add i (GroupMap.Range (2*(i-1)) (Some (2*(i-1)+1))) gm).
  Proof.
    intros gm WF_gm i i_INB. split.
    - apply wf_gm_add. + apply WF_gm. + auto.
    - unfold wf_gm_n, wf_gm_n_i. destruct WF_gm as [_ WF_gm]. unfold wf_gm_n in WF_gm.
      intros i' i'_INB.
      unfold GroupMap.find, GroupMap.add.
      rewrite GroupMap.Facts.add_neq_o by lia.
      apply WF_gm. auto.
  Qed.

  Lemma undef'_gm_add:
    forall gm i x gmpos k,
      gmpos = GroupMap.add i x gm -> i <= n ->
      (forall j, S n <= j -> j <= k + n -> GroupMap.find j gm = None) ->
      forall j, S n <= j -> j <= k + n -> GroupMap.find j gmpos = None.
  Proof.
    intros gm i x gmpos k -> i_INB UNDEF' j j_GE j_LE.
    unfold GroupMap.find, GroupMap.add.
    rewrite GroupMap.Facts.add_neq_o by lia.
    apply UNDEF'; auto.
  Qed.

  Lemma num_notexists_skipn_le:
    forall l i, num_notexists (skipn i l) <= num_notexists l.
  Proof.
    induction l.
    - intro i. simpl. destruct i; reflexivity.
    - intro i. simpl. destruct i; simpl; try reflexivity.
      specialize (IHl i).
      destruct a; lia.
  Qed.

  Theorem theRegex_aux_spec:
    (* We perform backwards induction on i ∈ {1, ..., n+1}. *)
    forall np1_minus_i i, i = n + 1 - np1_minus_i ->
    (* Let i ∈ {1, ..., n+1}. *)
    i <> 0 -> i <= n + 1 ->
      (* Let qtail be the list of the remaining quantifiers. *)
      forall qtail, qtail = List.skipn (i-1) quants ->
      (* Let gm be a valid group map... *)
      forall gm: group_map,
        wf_gm_poslk (length str) gm ->
        (* ... such that gm(i), gm(i+1), ..., gm(n) are undefined... *)
        (forall j, i <= j -> j <= n -> GroupMap.find j gm = None) ->
        (* ... and gm(n+1), ..., gm(n+ni) are undefined. *)
        (forall j, S n <= j -> j <= num_notexists qtail + n -> GroupMap.find j gm = None) ->
        forall inp t,
          (* Let inp := inp(2(i-1))... *)
          inp = inp_of_idx (2*(i-1)) ->
          (* ... and t := T(R(i), inp, gm, →). *)
          is_tree rer [Areg (theRegex_aux x_char semicolon_char n_char q i qtail)] inp gm forward t ->
          (* Then: *)
          (* - t has a leaf iff gm satisfies F_i *)
          (tree_leaves t gm inp forward <> [] <-> gm_satisfies_qbf_aux gm i qtail clauses = true) /\
          (* - for any leaf (inp', gm') of t, gm' and gm coincide on indices n+ni+1, ..., n+num_notexists quants. *)
          (forall inp' gm', In (inp', gm') (tree_leaves t gm inp forward) ->
            forall j, num_notexists qtail + 1 + n <= j -> j <= num_notexists quants + n -> GroupMap.find j gm = GroupMap.find j gm').
  Proof.
    induction np1_minus_i.
    - rewrite PeanoNat.Nat.sub_0_r. intros i -> _ _ qtail EQ_qtail.
      rewrite PeanoNat.Nat.add_sub in EQ_qtail. unfold n in EQ_qtail. rewrite skipn_all in EQ_qtail. subst qtail.
      intros gm WF_gm _ _.
      rewrite PeanoNat.Nat.add_sub.
      intros inp t EQ_inp TREE.
      pose proof check_conjunct_regex_spec q WF_q x_char semicolon_char n_char rer x_semicolon_neq inp gm EQ_inp.
      unfold wf_gm_poslk in WF_gm. destruct WF_gm as [WF_gm WF_gm_supp].
      specialize (H WF_gm t TREE _ eq_refl). destruct H. split; auto.
      intros inp' gm' IN_lf. specialize (H (inp', gm') IN_lf).
      injection H as EQ_inp' EQ_gm'. subst gm'. reflexivity.
    - intros i EQ_i i_NEQ_0 _ qtail EQ_qtail gm WF_gm UNDEF UNDEF' inp t EQ_inp TREE.
      specialize (IHnp1_minus_i (S i) ltac:(lia) ltac:(lia) ltac:(lia)).
      replace (S i - 1) with i in IHnp1_minus_i by lia.
      assert (EQ'_qtail: qtail = List.nth (i-1) quants Qbf.Exists :: List.skipn i quants). {
        rewrite EQ_qtail. replace i with (S (i-1)) at 3 by lia. apply skipn_head. fold n. lia.
      }
      rewrite EQ'_qtail. rewrite EQ'_qtail in TREE, UNDEF'.
      specialize (IHnp1_minus_i _ eq_refl).
      simpl gm_satisfies_qbf_aux.
      simpl theRegex_aux in TREE.
      destruct nth eqn:EQ_quant.
      + (* Exists *)
        inversion TREE. subst r1 r2 cont inp0 gm0 dir t0.
        rewrite app_nil_r in CONT. simpl in CONT.
        assert (exists tsub: tree, is_tree rer [Areg (def_var_regex x_char semicolon_char i)] inp gm forward tsub) as [tsub TREE_sub]. {
          eexists. apply compute_tr_is_tree.
        }
        pose proof leaves_concat rer inp gm forward [Areg (def_var_regex x_char semicolon_char i)] [Areg (theRegex_aux x_char semicolon_char n_char q (S i) (skipn i quants))] t tsub CONT TREE_sub as CONCAT.
        pose proof def_var_regex_spec q x_char semicolon_char n_char rer i inp i_NEQ_0 as DEF_SPEC.
        specialize_prove DEF_SPEC. { fold quants. fold n. lia. }
        specialize (DEF_SPEC EQ_inp tsub gm TREE_sub).
        rewrite DEF_SPEC in CONCAT. clear DEF_SPEC.
        remember (GroupMap.add i (GroupMap.Range (2*(i-1)) (Some (2*(i-1)+1))) gm) as gmpos.
        inversion CONCAT. subst x lbase f.
        inversion FM. subst x lbase f.
        inversion FM0. subst f lmapped0.
        inversion HEAD. subst act dir l.
        inversion HEAD0. subst act dir l.
        rewrite H4. rewrite H5.
        rewrite app_nil_r.
        simpl snd in H4, H5, TREE0, TREE1. simpl fst in H4, H5, TREE0, TREE1.
        clear HEAD HEAD0.
        specialize (IHnp1_minus_i gmpos) as IHpos. specialize (IHnp1_minus_i gm) as IHneg.
        clear IHnp1_minus_i.
        specialize_prove IHpos. {
          rewrite Heqgmpos. apply wf_gm_poslk_add. - auto. - lia.
        }
        specialize_prove IHpos. {
          eapply undef_gm_add with (gm := gm); eauto.
        }
        specialize_prove IHpos. {
          eapply undef'_gm_add with (gm := gm); eauto. lia.
        }
        specialize (IHpos (inp_of_idx (i + (i + 0))) t0 ltac:(reflexivity) ltac:(auto)).
        specialize (IHneg WF_gm).
        specialize_prove IHneg. { apply undef_gm_unchanged; auto. }
        specialize (IHneg ltac:(auto)).
        specialize (IHneg (inp_of_idx (i + (i + 0))) t1 ltac:(reflexivity) ltac:(auto)).
        pose proof app_nonempty_iff ly ly0.
        rewrite H0. clear H0.
        setoid_rewrite H4 in IHpos. setoid_rewrite H5 in IHneg.
        rewrite orb_true_iff.
        setoid_rewrite <- Heqgmpos. split.
        * tauto.
        * intros inp' gm' IN_lf. apply in_app_iff in IN_lf. simpl.
          destruct IHpos as [_ IHpos].
          destruct IHneg as [_ IHneg].
          specialize (IHpos inp' gm'). specialize (IHneg inp' gm'). destruct IN_lf; auto.
          intros j INB_j1 INB_j2. specialize (IHpos H0 j INB_j1 INB_j2). rewrite <- IHpos.
          rewrite Heqgmpos. symmetry. setoid_rewrite GroupMap.Facts.add_neq_o. 2: lia. reflexivity.
      + (* Not exists *)
        inversion TREE. subst r1 r2 cont inp0 gm0 dir t0. clear TREE.
        rewrite app_nil_r in CONT. simpl in CONT.
        pose proof inp_of_idx_even q x_char semicolon_char n_char (i-1) as EQ_inp'.
        specialize_prove EQ_inp'. { fold quants. fold n. lia. }
        fold (inp_of_idx (2*(i-1))) in EQ_inp'. rewrite <- EQ_inp in EQ_inp'.
        inversion CONT.
        2: {
          (* The capture_n_regex always captures the n at the end, so the lookaround cannot fail *)
          exfalso.
          subst lk r1 cont inp0 gm0 dir t.
          pose proof capture_n_regex_spec (length (fst q) + S (num_notexists (skipn i quants))) as CAP_N_SPEC. specialize (CAP_N_SPEC _ inp _ EQ_inp').
          inversion TREELK. subst r1 r2 cont inp0 gm0 dir treelk.
          specialize (CAP_N_SPEC gm t2 ISTREE2).
          unfold lk_result in FAIL_LK. simpl in FAIL_LK.
          rewrite first_tree_leaf with (t := t2) in FAIL_LK. rewrite CAP_N_SPEC in FAIL_LK.
          destruct (tree_res t1 gm inp forward) as [[]|]; try discriminate.
        }
        subst lk r1 cont inp0 gm0 dir t. clear CONT.
        inversion TREELK. subst r1 r2 cont inp0 gm0 dir treelk. clear TREELK.
        simpl. unfold lk_result in RES_LK. simpl in RES_LK.
        (* Specializing IHnp1_minus_i *)
        inversion ISTREE1. subst r1 r2 cont inp0 gm0 dir t1. clear ISTREE1.
        rewrite app_nil_r in CONT. simpl in CONT.
        assert (exists tsub: tree, is_tree rer [Areg (def_var_regex x_char semicolon_char i)] inp gm forward tsub) as [tsub TREE_sub]. {
          eexists. apply compute_tr_is_tree.
        }
        pose proof leaves_concat rer inp gm forward [Areg (def_var_regex x_char semicolon_char i)] [Areg (theRegex_aux x_char semicolon_char n_char q (S i) (skipn i quants))] t tsub CONT TREE_sub as CONCAT.
        pose proof def_var_regex_spec q x_char semicolon_char n_char rer i inp i_NEQ_0 as DEF_SPEC.
        specialize_prove DEF_SPEC. { fold quants. fold n. lia. }
        specialize (DEF_SPEC EQ_inp tsub gm TREE_sub).
        rewrite DEF_SPEC in CONCAT. clear DEF_SPEC.
        remember (GroupMap.add i (GroupMap.Range (2*(i-1)) (Some (2*(i-1)+1))) gm) as gmpos.
        inversion CONCAT. subst x lbase f. clear CONCAT.
        inversion FM. subst x lbase f. clear FM.
        inversion FM0. subst f lmapped0. clear FM0.
        inversion HEAD. subst act dir l. clear HEAD.
        inversion HEAD0. subst act dir l. clear HEAD0.
        rewrite H4. rewrite H5.
        rewrite app_nil_r.
        simpl snd in H4, H5, TREE, TREE0. simpl fst in H4, H5, TREE, TREE0.
        specialize (IHnp1_minus_i gmpos) as IHpos. specialize (IHnp1_minus_i gm) as IHneg.
        clear IHnp1_minus_i.
        specialize_prove IHpos. {
          rewrite Heqgmpos. apply wf_gm_poslk_add. - auto. - lia.
        }
        specialize_prove IHpos. {
          eapply undef_gm_add with (gm := gm); eauto.
        }
        specialize_prove IHpos. {
          eapply undef'_gm_add with (gm := gm); eauto.
          - lia.
          - intros j INB_j1 INB_j2. apply UNDEF'; simpl; lia.
        }
        specialize (IHpos (inp_of_idx (i + (i + 0))) t0 ltac:(reflexivity) ltac:(auto)).
        specialize (IHneg WF_gm).
        specialize_prove IHneg. { apply undef_gm_unchanged; auto. }
        specialize_prove IHneg. {
          intros j INB_j1 INB_j2. apply UNDEF'; simpl; lia.
        }
        specialize (IHneg (inp_of_idx (i + (i + 0))) t1 ltac:(reflexivity) ltac:(auto)).
        setoid_rewrite H4 in IHpos. setoid_rewrite H5 in IHneg.
        (* End specializing IHnp1_minus_i *)
        pose proof capture_n_regex_spec (length (fst q) + S (num_notexists (skipn i quants))) as CAP_N_SPEC.
        specialize (CAP_N_SPEC _ inp _ EQ_inp' _ _ ISTREE2). rewrite CAP_N_SPEC.
        pose proof app_nonempty_iff ly ly0.
        (* About check_n_regex *)
        pose proof check_n_regex_spec (length (fst q) + S (num_notexists (skipn i quants))) _ inp _ ltac:(fold quants; fold n; lia) EQ_inp' as CHECK_N_SPEC.
        destruct (ly ++ ly0) as [|lfnonneg ?] eqn:NONNEG_EMPTY.
        * (* Non-negated QBF is false: we capture the n at the end. Prove True <-> True *)
          simpl.
          set (gmsetn := GroupMap.add (length (fst q) + _) _ gm).
          specialize (CHECK_N_SPEC gmsetn).
          specialize_prove CHECK_N_SPEC. {
            unfold gmsetn, wf_gm_n_i.
            right. setoid_rewrite GroupMap.Facts.add_eq_o; reflexivity.
          }
          rewrite first_tree_leaf, <- H, <- H3, app_nil_r, NONNEG_EMPTY in RES_LK.
          simpl in RES_LK.
          rewrite first_tree_leaf, CAP_N_SPEC in RES_LK. simpl in RES_LK.
          injection RES_LK as <-.
          specialize (CHECK_N_SPEC treecont TREECONT).
          split.
          -- transitivity True; split; auto; intros _.
             ++ apply CHECK_N_SPEC. unfold gmsetn.
                apply GroupMap.Facts.add_eq_o. reflexivity.
             ++ destruct ly eqn:LY_NIL; try discriminate.
                destruct ly0 eqn:LY0_NIL; try discriminate.
                clear NONNEG_EMPTY H0.
                destruct IHpos as [IHpos _]. destruct IHneg as [IHneg _].
                setoid_rewrite <- Heqgmpos.
                assert (nil (A := leaf) <> [] <-> False). {
                  split; try contradiction.
                }
                rewrite H0 in IHpos, IHneg.
                apply proj2 in IHpos, IHneg.
                destruct gm_satisfies_qbf_aux; try contradiction. destruct gm_satisfies_qbf_aux; try contradiction. reflexivity.
          -- apply proj2 in CHECK_N_SPEC.
             intros inp' gm' IN_lf'.
             specialize (CHECK_N_SPEC (inp', gm') IN_lf').
             injection CHECK_N_SPEC as _ ->.
             intros j INB_j1 INB_j2. unfold gmsetn.
             fold quants. fold n. symmetry.
             apply GroupMap.Facts.add_neq_o. lia.
        * (* Non-negated QBF is true: we don't capture the n at the end. *)
          set (leaves := match (lfnonneg :: l) ++ _ with | [] => _ | (_, gm') :: _ => _ end).
          assert (leaves = []). {
            destruct lfnonneg as [inpnneg gmnneg]. simpl in leaves.
            assert (In (inpnneg, gmnneg) ly \/ In (inpnneg, gmnneg) ly0). {
              apply in_app_or. setoid_rewrite NONNEG_EMPTY. left. reflexivity.
            }
            destruct H1.
            - apply proj2 in IHpos. clear IHneg.
              rewrite first_tree_leaf, <- H, <- H3, app_nil_r, NONNEG_EMPTY in RES_LK. simpl in RES_LK.
              injection RES_LK as <-.
              specialize (IHpos inpnneg gmnneg H1 (length (fst q) + S (num_notexists (skipn i quants)))).
              specialize_prove IHpos. {
                fold quants. fold n. lia.
              }
              specialize_prove IHpos. {
                fold quants. fold n. rewrite PeanoNat.Nat.add_comm.
                apply Nat.add_le_mono_r.
                change (S _) with (num_notexists (NotExists :: skipn i quants)).
                rewrite <- EQ'_qtail, EQ_qtail. apply num_notexists_skipn_le. (* num_notexists of a tail is at most num_notexists of the entire list *)
              }
              specialize CHECK_N_SPEC with (gm := gmnneg) (t := treecont) (2 := TREECONT).
              unfold wf_gm_n_i in CHECK_N_SPEC.
              assert (GroupMap.find (length (fst q) + S (num_notexists (skipn i quants))) gmnneg = None). {
                rewrite <- IHpos, Heqgmpos.
                fold quants. fold n.
                setoid_rewrite GroupMap.Facts.add_neq_o; try lia.
                apply UNDEF'; simpl; lia.
              }
              specialize_prove CHECK_N_SPEC. {
                left. auto.
              }
              unfold leaves.
              apply proj1 in CHECK_N_SPEC.
              rewrite H2 in CHECK_N_SPEC.
              destruct (tree_leaves treecont gmnneg inp forward); try reflexivity.
              exfalso. apply proj1 in CHECK_N_SPEC. specialize (CHECK_N_SPEC ltac:(discriminate)). discriminate.
            - apply proj2 in IHneg. clear IHpos.
              rewrite first_tree_leaf, <- H, <- H3, app_nil_r, NONNEG_EMPTY in RES_LK. simpl in RES_LK.
              injection RES_LK as <-.
              specialize (IHneg inpnneg gmnneg H1 (length (fst q) + S (num_notexists (skipn i quants)))).
              specialize_prove IHneg. {
                fold quants. fold n. lia.
              }
              specialize_prove IHneg. {
                fold quants. fold n. rewrite PeanoNat.Nat.add_comm.
                apply Nat.add_le_mono_r.
                change (S _) with (num_notexists (NotExists :: skipn i quants)).
                rewrite <- EQ'_qtail, EQ_qtail. apply num_notexists_skipn_le. (* num_notexists of a tail is at most num_notexists of the entire list *)
              }
              specialize CHECK_N_SPEC with (gm := gmnneg) (t := treecont) (2 := TREECONT).
              unfold wf_gm_n_i in CHECK_N_SPEC.
              assert (GroupMap.find (length (fst q) + S (num_notexists (skipn i quants))) gmnneg = None). {
                rewrite <- IHneg.
                fold quants. fold n.
                apply UNDEF'; simpl; lia.
              }
              specialize_prove CHECK_N_SPEC. {
                left. auto.
              }
              unfold leaves.
              apply proj1 in CHECK_N_SPEC.
              rewrite H2 in CHECK_N_SPEC.
              destruct (tree_leaves treecont gmnneg inp forward); try reflexivity.
              exfalso. apply proj1 in CHECK_N_SPEC. specialize (CHECK_N_SPEC ltac:(discriminate)). discriminate.
          }
          rewrite H1. clear H1.
          split. 2: { intros inp' gm' H'. inversion H'. }
          apply proj1 in IHpos, IHneg.
          apply proj1 in H0. specialize (H0 ltac:(discriminate)).
          split; try contradiction.
          destruct H0.
          -- apply IHpos in H0.
             setoid_rewrite <- Heqgmpos. rewrite H0. simpl. rewrite andb_false_r. discriminate.
          -- apply IHneg in H0.
             rewrite H0. simpl. discriminate. 
  Qed.

  Theorem qbf_regex:
    regex_matches_string rer (theRegex x_char semicolon_char n_char q) str <->
    qbf_valid q = true.
  Proof.
  Admitted.

End HardnessPoslk.