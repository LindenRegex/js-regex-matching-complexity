From Linden Require Import Regex Chars Parameters Groups Tree Semantics Tactics.
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

  Hypothesis (x_semicolon_neq: Character.canonicalize rer x_char <>
    Character.canonicalize rer semicolon_char).
  Hypothesis (x_n_neq: Character.canonicalize rer x_char <>
    Character.canonicalize rer n_char).
  Hypothesis (semicolon_n_neq: Character.canonicalize rer semicolon_char <>
    Character.canonicalize rer n_char).
  Hypothesis (n_not_lineterminator: ~In n_char Character.line_terminators).
  Hypothesis (x_not_lineterminator: ~In x_char Character.line_terminators).

  Let str := theString x_char semicolon_char n_char q.
  Let quants := fst q.
  Let clauses := snd q.
  Let n := length quants.

  Definition inp_of_idx (i: nat) :=
    Input (List.skipn i str) (List.rev (List.firstn i str)).

  Definition wf_gm_n (strlen: nat) (gm: group_map): Prop :=
    forall i, i >= S n ->
      GroupMap.find i gm = None \/
      GroupMap.find i gm = Some (GroupMap.Range (strlen - 1) (Some strlen)).

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
      forall gm, wf_gm_n (length (input_str inp)) gm ->
        forall t, is_tree rer [Areg (check_n_regex x_char semicolon_char gid)] inp gm forward t ->
          tree_leaves t gm inp forward <> [] <-> GroupMap.find gid gm = Some (GroupMap.Range (length (input_str inp) - 1) (Some (length (input_str inp)))).
  Proof.
    intros gid k. induction k.
    - simpl. intros inp pref VALID_gid -> gm WF_gm t TREE.
      unfold wf_gm_n in WF_gm. specialize (WF_gm gid VALID_gid).
      destruct WF_gm as [NONE | SOME].
      + (* Prove False <-> False *)
        split; try congruence.
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
        simpl. contradiction.
      + (* Prove True <-> True *)
        split; auto. intros _.
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
        simpl. discriminate.
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
      unfold advance_input'. simpl. rewrite IHk.
      simpl. do 2 rewrite <- app_assoc. simpl. reflexivity.
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
          (* - t has a leaf iff gm satisfies F_i. *)
          (tree_leaves t gm inp forward <> [] <-> gm_satisfies_qbf_aux gm i qtail clauses = true).
  Proof.
  Admitted.

  Theorem qbf_regex:
    regex_matches_string rer (theRegex x_char semicolon_char n_char q) str <->
    qbf_valid q = true.
  Proof.
  Admitted.

End HardnessPoslk.