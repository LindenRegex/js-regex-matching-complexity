From JsRegexOptp Require Import RegexEncoding Qbf GroupMaps.
From Linden Require Import Parameters Chars Groups Semantics Tree Tactics.
From Linden.Rewriting Require Import ProofSetup.
From Warblre Require Import Parameters RegExpRecord Base.
Require Import List Lia.
Import ListNotations.

Section Proofs.
  Context {params: LindenParameters}.
  Context (q: qbf).
  Hypothesis (WF_q: wf_qbf q).

  Context (x_char semicolon_char: Parameters.Character).
  Context (rer: RegExpRecord).
  Hypothesis (x_semicolon_neq: Character.canonicalize rer x_char <>
    Character.canonicalize rer semicolon_char).

  (* The string *)
  Let str := theString q x_char semicolon_char.
  (* Number of variables *)
  Let n := List.length (fst q).
  (* The quantifiers *)
  Let quants := fst q.
  (* Number of clauses *)
  Let m := List.length (snd q).
  (* The clauses *)
  Let clauses := snd q.

  Definition inp_of_idx (i: nat) :=
    Input (List.skipn i str) (List.rev (List.firstn i str)).

  Lemma list_sum_repeat:
    forall k n: nat, list_sum (repeat k n) = n*k.
  Proof.
    clear n. induction n.
    - simpl. reflexivity.
    - simpl. rewrite IHn0. reflexivity.
  Qed.

  Lemma str_len: length str = 2*(n+m).
  Proof.
    unfold str, theString.
    rewrite concat_length, map_repeat. simpl.
    fold n m.
    rewrite list_sum_repeat. lia.
  Qed.

  Lemma inp_of_idx_even:
    forall i, i <= n + m ->
      inp_of_idx (2*i) = Input
        (List.concat (List.repeat [x_char; semicolon_char] (n+m-i)))
        (List.concat (List.repeat [semicolon_char; x_char] i)).
  Proof.
  Admitted.

  Lemma input_str_inp_of_idx:
    forall i, input_str (inp_of_idx i) = str.
  Admitted.

  Lemma idx_inp_of_idx:
    forall i, i <= length str -> idx (inp_of_idx i) = i.
  Admitted.

  Lemma advance_input_inp_of_idx:
    forall i, i < length str ->
      advance_input' (inp_of_idx i) forward = inp_of_idx (S i).
  Admitted.

  Lemma substr_var:
    forall v, wf_var n v ->
      forall i, substr (inp_of_idx i) (2*(v-1)) (2*(v-1)+1) = [x_char].
  Proof.
    intros v WF_v i. unfold inp_of_idx, substr.
    replace (2*(v-1)+1-2*(v-1)) with 1 by lia.
    setoid_rewrite input_str_inp_of_idx.
    unfold wf_var in WF_v. assert (WF_v': v - 1 < n) by lia.
    unfold str, theString.
  Admitted.

  Lemma read_backref_var_sat:
    forall (gm: group_map) (v: variable) (i: nat),
      i < m -> wf_var n v -> wf_gm gm ->
      gm_satisfies_var gm v = true -> read_backref rer gm v (inp_of_idx (2*(n+i))) forward = Some ([x_char], inp_of_idx (2*(n+i)+1)).
  Proof.
    intros gm v i INB_i WF_v WF_GM SAT.
    destruct (WF_GM v) as [FOUND|NOTFOUND].
    {
      unfold gm_satisfies_var in SAT. rewrite FOUND in SAT. discriminate.
    }
    unfold read_backref. rewrite NOTFOUND.
    rewrite inp_of_idx_even at 1. 2: lia.
    rewrite concat_length, map_repeat, list_sum_repeat. simpl length.
    replace (2*(v-1)+1-2*(v-1)) with 1 by lia.
    replace (S _ <=? 1) with false. 2: {
      symmetry. rewrite PeanoNat.Nat.leb_gt. lia.
    }
    replace (n+m-(n+i)) with (m-i) by lia.
    rewrite substr_var.
  Admitted.

  Lemma read_backref_var_unsat:
    forall (gm: group_map) (v: variable) (i: nat),
      i < m -> wf_gm gm ->
      gm_satisfies_var gm v = false -> read_backref rer gm v (inp_of_idx (2*(n+i))) forward = Some ([], inp_of_idx (2*(n+i))).
  Proof.
    intros gm v i INB_i WF_GM UNSAT. unfold gm_satisfies_var in UNSAT.
    unfold read_backref. destruct GroupMap.find; try discriminate. reflexivity.
  Qed.


  Lemma check_literal_regex_spec:
    forall (i: nat) (lit: literal) (inp: input) (gm: group_map),
      i < m -> wf_literal n lit ->
      inp = inp_of_idx (2*(n+i)) -> wf_gm gm ->
        forall t, is_tree rer [Areg (check_literal_regex x_char lit)] inp gm forward t ->
          forall lflist, lflist = tree_leaves t gm inp forward ->
            (gm_satisfies_lit gm lit = true -> lflist = [(inp_of_idx (2*(n+i)+1), gm)]) /\
            (gm_satisfies_lit gm lit = false -> lflist = [] \/ lflist = [(inp, gm)]).
  Proof.
    intros i lit inp gm INB_i WF_lit EQ_inp WF_GM t TREE lflist EQ_lflist.
    destruct lit as [v|v]; simpl in *.
    - (* Positive variable *)
      destruct (WF_GM v) as [NOTFOUND | FOUND].
      + (* Variable not found *)
        split; intro SAT.
        1: { unfold gm_satisfies_var in SAT. rewrite NOTFOUND in SAT. discriminate. }
        inversion TREE; subst.
        2: { unfold read_backref in READ_BACKREF. rewrite NOTFOUND in READ_BACKREF. discriminate. }
        unfold read_backref in READ_BACKREF. rewrite NOTFOUND in READ_BACKREF.
        injection READ_BACKREF as <- <-.
        inversion TREECONT; subst. simpl.
        right. reflexivity.
      + (* Variable found *)
        destruct gm_satisfies_var eqn:SAT.
        2: { unfold gm_satisfies_var in SAT. rewrite FOUND in SAT. discriminate. }
        split; try discriminate. intros _.
        inversion TREE; subst.
        2: {
          rewrite read_backref_var_sat with (i := i) in READ_BACKREF; auto.
          2: { inversion WF_lit; subst. auto. }
          discriminate.
        }
        rewrite read_backref_var_sat with (i := i) in READ_BACKREF; auto.
        2: { inversion WF_lit; subst. auto. }
        injection READ_BACKREF as <- <-.
        inversion TREECONT; subst. simpl. f_equal. admit.
    - (* Negative variable *)
      destruct (WF_GM v) as [NOTFOUND|FOUND].
      + (* Variable not found *)
        destruct gm_satisfies_var eqn:SAT.
        1: { unfold gm_satisfies_var in SAT. rewrite NOTFOUND in SAT. discriminate. }
        split; try discriminate. intros _.
        inversion TREE; subst. simpl in CONT. inversion CONT; subst.
        2: { rewrite read_backref_var_unsat with (i := i) in READ_BACKREF; auto. discriminate. }
        rewrite read_backref_var_unsat with (i := i) in READ_BACKREF; auto. injection READ_BACKREF as <- <-.
        inversion TREECONT; subst.
        2: { (* The read cannot fail *) exfalso. admit. }
        inversion TREECONT0; subst. simpl. f_equal. admit.
      + (* Variable found *)
        destruct gm_satisfies_var eqn:SAT.
        2: { unfold gm_satisfies_var in SAT. rewrite FOUND in SAT. discriminate. }
        split; try discriminate. intros _.
        inversion TREE; subst. simpl in CONT. inversion CONT; subst.
        2: { rewrite read_backref_var_sat with (i := i) in READ_BACKREF; auto. inversion WF_lit; subst. auto. }
        rewrite read_backref_var_sat with (i := i) in READ_BACKREF; auto. 2: { inversion WF_lit; subst. auto. }
        injection READ_BACKREF as <- <-.
        inversion TREECONT; subst.
        1: { (* The read cannot succeed *) exfalso. admit. }
        left. reflexivity.
  Admitted.

  Lemma check_clause_regex_aux_spec:
    forall (i: nat) (c: clause) (inp: input) (gm: group_map),
      i < m -> wf_clause n c ->
      inp = inp_of_idx (2*(n+i)) -> wf_gm gm ->
      forall t, is_tree rer [Areg (check_clause_regex_aux x_char c)] inp gm forward t ->
        forall lflist, lflist = tree_leaves t gm inp forward ->
          (forall lf, In lf lflist -> lf = (inp_of_idx (2*(n+i)+1), gm) \/ lf = (inp, gm)) /\
          (In (inp_of_idx (2*(n+i)+1), gm) lflist <-> gm_satisfies_clause gm c = true).
  Proof.
    induction c as [|l c IH]; intros inp gm INB_i WF_c EQ_inp WF_GM t TREE lflist EQ_lflist.
    - simpl in TREE. inversion TREE; subst. inversion ISTREE; subst.
      simpl. split.
      + intros lf [EQ_lf|[]]. subst lf. right. reflexivity.
      + split; try discriminate. intros [H|[]]. admit.
    - simpl in TREE. inversion TREE; subst r1 r2 cont inp0 gm0 dir t.
      unfold wf_clause in WF_c, IH. inversion WF_c as [|l' c' WF_l WF_c']; subst l' c'.
      specialize (IH inp gm INB_i WF_c' EQ_inp WF_GM t2 ISTREE2).
      subst lflist. simpl.
      specialize (IH _ eq_refl).
      pose proof check_literal_regex_spec i l inp gm INB_i WF_l EQ_inp WF_GM t1 ISTREE1 _ eq_refl as l_SPEC.
      split.
      + intro lf. rewrite in_app_iff. intros [IN_1 | IN_2].
        * (* Left case *)
          destruct gm_satisfies_lit; destruct l_SPEC as [l_SPEC_sat l_SPEC_unsat].
          -- rewrite l_SPEC_sat in IN_1 by reflexivity. simpl in IN_1. destruct IN_1 as [IN_1|[]].
             subst lf. left. reflexivity.
          -- destruct (l_SPEC_unsat eq_refl) as [l_SPEC_unsat' | l_SPEC_unsat'].
             ++ rewrite l_SPEC_unsat' in IN_1. destruct IN_1.
             ++ rewrite l_SPEC_unsat' in IN_1. destruct IN_1 as [IN_1|[]]. subst lf. right. reflexivity.
        * (* Right case *) apply IH; auto.
      + rewrite in_app_iff, (proj2 IH), Bool.orb_true_iff.
        assert (l_SPEC': gm_satisfies_lit gm l = true <-> In (inp_of_idx (2*(n+i)+1), gm) (tree_leaves t1 gm inp forward)).
        {
          destruct gm_satisfies_lit.
          - destruct l_SPEC as [l_SPEC _]. rewrite (l_SPEC eq_refl). split; auto. intro. left. reflexivity.
          - destruct l_SPEC as [_ l_SPEC]. destruct (l_SPEC eq_refl) as [l_SPEC'|l_SPEC'].
            + rewrite l_SPEC'. simpl. split; auto; discriminate.
            + rewrite l_SPEC'. simpl. admit.
        }
        tauto.
  Admitted.

  Lemma FlatMap_in_r {X Y: Type}:
    forall (lx: list X) (f: X -> list Y -> Prop) (ly: list Y),
      FlatMap.determ f -> FlatMap.FlatMap lx f ly ->
      forall y: Y, 
        In y ly <-> 
          exists (x: X) (fx: list Y),
            In x lx /\ f x fx /\ In y fx.
  Proof.
    intros lx f ly DETERM. induction 1.
    - simpl. firstorder.
    - specialize (IHFlatMap DETERM). intro y. specialize (IHFlatMap y).
      rewrite in_app_iff. simpl.
      split; intro H1.
      + destruct H1 as [H1|H1].
        * exists x. exists ly. split. { left. reflexivity. } auto.
        * firstorder.
      + destruct H1 as [x0 [fx0 [[<- | H1] [H2 H3]]]].
        * specialize (DETERM x ly fx0 HEAD H2). subst fx0. auto.
        * firstorder.
  Qed.

  Lemma check_clause_regex_spec:
    forall (i: nat) (c: clause) (inp: input) (gm: group_map),
      i < m -> wf_clause n c ->
      inp = inp_of_idx (2*(n+i)) -> wf_gm gm ->
      forall t, is_tree rer [Areg (check_clause_regex x_char semicolon_char c)] inp gm forward t ->
        forall lflist, lflist = tree_leaves t gm inp forward ->
          (forall lf, In lf lflist -> lf = (inp_of_idx (2*(n+i+1)), gm)) /\
          (lflist <> nil <-> gm_satisfies_clause gm c = true).
  Proof.
    intros i c inp gm INB_i WF_c EQ_inp WF_GM t TREE lflist EQ_lflist.
    unfold check_clause_regex in TREE.
    inversion TREE; subst r1 r2 cont inp0 gm0 dir t0. rewrite app_nil_r in CONT.
    simpl in CONT.
    pose proof leaves_concat rer inp gm forward [Areg (check_clause_regex_aux x_char c)]
      [Areg (Regex.Character (CdSingle semicolon_char))] t as CONCAT.
    assert (exists taux: tree, is_tree rer [Areg (check_clause_regex_aux x_char c)] inp gm forward taux). {
      eexists. apply compute_tr_is_tree.
    }
    destruct H as [taux TREE_aux].
    specialize (CONCAT taux CONT TREE_aux).
    pose proof check_clause_regex_aux_spec i c inp gm INB_i WF_c EQ_inp WF_GM taux TREE_aux _ eq_refl
      as [AUX_FORM AUX_SUCC_IFF].
    assert (H: forall lf, In lf lflist -> lf = (inp_of_idx (2*(n+i+1)), gm)). {
      intros lf IN_lf. subst lflist.
      rewrite @FlatMap_in_r with (X := leaf) (2 := CONCAT) in IN_lf.
      2: apply act_from_leaf_determ.
      destruct IN_lf as [x [fx [IN_x [ACT_FROM_LEAF_x IN_lf]]]].
      inversion ACT_FROM_LEAF_x; subst act dir l fx.
      specialize (AUX_FORM x IN_x). destruct AUX_FORM as [AUX_FORM | AUX_FORM]; subst x.
      - simpl in *. inversion TREE0; subst.
        2: { (* Read never fails *) exfalso. admit. }
        inversion TREECONT; subst. simpl in IN_lf.
        destruct IN_lf as [IN_lf|[]]. subst lf. f_equal. admit.
      - simpl in *. inversion TREE0; subst.
        1: { (* Read never succeeds *) exfalso. admit. }
        simpl in IN_lf. destruct IN_lf.
    }
    split; auto.
  Admitted.

  Lemma FlatMap_empty_iff {X Y: Type}:
    forall (lx: list X) (f: X -> list Y -> Prop) (ly: list Y),
      FlatMap.determ f -> FlatMap.FlatMap lx f ly ->
      (ly <> [] <-> exists (x: X) (fx: list Y), In x lx /\ f x fx /\ fx <> []).
  Proof.
    intros lx f ly DETERM. induction 1.
    - simpl. firstorder.
    - specialize (IHFlatMap DETERM).
      destruct ly as [|y ly].
      + simpl. rewrite IHFlatMap. split; try solve[firstorder].
        intros [x0 [fx H0]].
        destruct H0. destruct H0.
        * subst x0. exfalso. specialize (DETERM x [] fx).
          rewrite <- DETERM in H1 by tauto. destruct H1. contradiction.
        * firstorder.
      + split. 2: rewrite <- app_comm_cons; discriminate.
        intros _. exists x. exists (y :: ly). split.
        * left. reflexivity.
        * split; [auto|discriminate].
  Qed.

  Lemma check_conjunct_regex_spec:
    forall (inp: input) (gm: group_map),
      inp = inp_of_idx (2*n) -> wf_gm gm ->
      forall t, is_tree rer [Areg (check_conjunct_regex x_char semicolon_char (rev clauses))] inp gm forward t ->
        forall lflist, lflist = tree_leaves t gm inp forward ->
          (forall lf, In lf lflist -> lf = (inp_of_idx (2*(n+m)), gm)) /\
          (lflist <> nil <-> gm_satisfies_conjunct gm clauses = true).
  Proof.
    intros inp gm EQ_inp WF_GM. unfold m. fold clauses.
    assert (LE_length_clauses: length clauses <= m). { reflexivity. }
    revert LE_length_clauses.
    assert (WF_clauses: Forall (wf_clause n) clauses). { inversion WF_q; subst. apply H. }
    revert WF_clauses. generalize clauses. induction clauses0 using rev_ind.
    - simpl. intros ? ? t TREE lflist EQ_lflist.
      inversion TREE. subst cont inp0 gm0 dir tcont.
      inversion ISTREE. subst inp0 gm0 dir t. simpl in EQ_lflist. subst lflist.
      split.
      + intros lf [EQ_lf|[]]. subst lf inp. f_equal. f_equal. lia.
      + split. * reflexivity. * discriminate.
    - rewrite app_length, rev_app_distr. simpl.
      intros ? ? t TREE lflist EQ_lflist.
      inversion TREE. subst r1 r2 cont inp0 gm0 dir t0.
      rewrite app_nil_r in CONT. simpl in CONT.
      assert (SUBTREE: exists tsub: tree, is_tree rer [Areg (check_conjunct_regex x_char semicolon_char (rev clauses0))] inp gm forward tsub). {
        eexists. apply compute_tr_is_tree.
      }
      destruct SUBTREE as [tsub SUBTREE].
      specialize_prove IHclauses0. { rewrite Forall_app in WF_clauses. tauto. }
      specialize (IHclauses0 ltac:(lia) tsub SUBTREE).
      pose proof leaves_concat rer inp gm forward [Areg (check_conjunct_regex x_char semicolon_char (rev clauses0))] [Areg (check_clause_regex x_char semicolon_char x)] _ _ CONT SUBTREE as CONCAT.
      rewrite <- EQ_lflist in CONCAT.
      remember (tree_leaves tsub gm inp forward) as lflist_sub. specialize (IHclauses0 lflist_sub eq_refl).
      pose proof check_clause_regex_spec (length clauses0) x as SPEC_check_x. 
      split.
      + intros lf IN_lf. rewrite @FlatMap_in_r with (X := leaf) in IN_lf.
        3: apply CONCAT. 2: apply act_from_leaf_determ.
        destruct IN_lf as [lfsub [lflist_clause [IN_lfsub [TREE_clause IN_lf]]]].
        inversion TREE_clause. subst act dir l.
        specialize (SPEC_check_x (fst lfsub) (snd lfsub) ltac:(lia)).
        specialize_prove SPEC_check_x. {
          rewrite Forall_app in WF_clauses.
          destruct WF_clauses as [_ WF_clauses].
          inversion WF_clauses. auto.
        }
        destruct IHclauses0 as [IHclauses0_0 IHclauses0_1].
        specialize (IHclauses0_0 lfsub IN_lfsub).
        specialize_prove SPEC_check_x. {
          rewrite IHclauses0_0. reflexivity.
        }
        specialize_prove SPEC_check_x. {
          rewrite IHclauses0_0. auto.
        }
        specialize (SPEC_check_x t0 TREE0 lflist_clause).
        symmetry in H2. specialize (SPEC_check_x H2).
        destruct SPEC_check_x as [SPEC_check_x _].
        specialize (SPEC_check_x lf IN_lf).
        rewrite SPEC_check_x. f_equal. 2: rewrite IHclauses0_0; reflexivity. f_equal. lia.
      + rewrite (FlatMap_empty_iff lflist_sub _ lflist ltac:(apply act_from_leaf_determ) CONCAT).
        split; intro.
        * destruct H as [lfsub [lflist_clause [IN_lfsub [TREE_clause lflist_clause_nonempty]]]].
          inversion TREE_clause. subst act dir l. symmetry in H2.
          specialize (SPEC_check_x (fst lfsub) (snd lfsub) ltac:(lia)).
          specialize_prove SPEC_check_x. {
            rewrite Forall_app in WF_clauses.
            destruct WF_clauses as [_ WF_clauses].
            inversion WF_clauses. auto.
          }
          destruct IHclauses0 as [IHclauses0_0 IHclauses0_1].
          specialize (IHclauses0_0 lfsub IN_lfsub).
          specialize_prove SPEC_check_x. {
            rewrite IHclauses0_0. reflexivity.
          }
          specialize_prove SPEC_check_x. {
            rewrite IHclauses0_0. auto.
          }
          specialize (SPEC_check_x t0 TREE0 lflist_clause H2).
          destruct IHclauses0_1 as [IHclauses0_1 _].
          specialize_prove IHclauses0_1. {
            destruct lflist_sub; try discriminate. destruct IN_lfsub.
          }
          destruct SPEC_check_x as [_ SPEC_check_x].
          unfold gm_satisfies_conjunct.
          rewrite forallb_app. unfold gm_satisfies_conjunct in IHclauses0_1.
          rewrite IHclauses0_1. simpl.
          destruct SPEC_check_x as [SPEC_check_x _].
          specialize (SPEC_check_x lflist_clause_nonempty).
          rewrite IHclauses0_0 in SPEC_check_x. simpl in SPEC_check_x. rewrite SPEC_check_x. reflexivity.
        * unfold gm_satisfies_conjunct in *. rewrite forallb_app in H.
          apply andb_true_iff in H. destruct H as [clauses0_sat x_sat].
          simpl in x_sat. rewrite andb_true_r in x_sat.
          destruct IHclauses0 as [IHclauses0_0 [_ IHclauses0_1]].
          specialize (IHclauses0_1 clauses0_sat).
          destruct lflist_sub as [|[inpsub gmsub] lflist_sub]; try contradiction.
          specialize (IHclauses0_0 (inpsub, gmsub) ltac:(left; reflexivity)).
          injection IHclauses0_0 as EQ_inpsub ->.
          specialize (SPEC_check_x inpsub gm ltac:(lia)).
          specialize_prove SPEC_check_x. {
            rewrite Forall_app in WF_clauses.
            destruct WF_clauses as [_ WF_clauses].
            inversion WF_clauses. auto.
          }
          specialize (SPEC_check_x EQ_inpsub WF_GM).
          assert (exists t: tree, is_tree rer [Areg (check_clause_regex x_char semicolon_char x)] inpsub gm forward t). {
            eexists. apply compute_tr_is_tree.
          }
          destruct H as [tclause TREE_clause].
          specialize (SPEC_check_x tclause TREE_clause).
          remember (tree_leaves tclause gm inpsub forward) as lflist_clause.
          specialize (SPEC_check_x _ eq_refl).
          exists (inpsub, gm). exists lflist_clause. split. 1: left; reflexivity.
          split.
          -- rewrite Heqlflist_clause. constructor. auto.
          -- destruct SPEC_check_x as [_ SPEC_check_x]. tauto.
  Qed.

  Lemma def_var_regex_spec:
    forall (i: nat) (inp: input),
      i <> 0 -> i <= n -> inp = inp_of_idx (2*(i-1)) ->
      forall (t: tree) (gm: group_map),
        is_tree rer [Areg (def_var_regex x_char semicolon_char i)] inp gm forward t ->
        tree_leaves t gm inp forward = [
          (inp_of_idx (2*i), GroupMap.add i (GroupMap.Range (2*(i-1)) (Some (2*(i-1)+1))) gm);
          (inp_of_idx (2*i), gm)].
  Proof.
    intros i inp i_NEQ_0 i_INB EQ_inp t gm TREE.
    unfold def_var_regex in TREE.
    inversion TREE. subst r1 r2 cont inp0 gm0 dir t0.
    rewrite app_nil_r in CONT. simpl in CONT.
    inversion CONT. subst r1 r2 cont inp0 gm0 dir t.
    inversion ISTREE1. subst gid r1 cont inp0 gm0 dir t1.
    inversion TREECONT.
    2: { subst cd cont inp0 gm0 dir treecont. exfalso. admit. }
    subst cd cont inp0 gm0 dir treecont.
    inversion TREECONT0. subst gid cont inp0 gm0 dir tcont.
    inversion TREECONT1. 2: { subst cd cont inp0 gm0 dir treecont. exfalso. admit. }
    subst cd cont inp0 gm0 dir treecont.
    inversion TREECONT2. subst inp0 gm0 dir tcont.
    inversion ISTREE2. 2: { subst cd cont inp0 gm0 dir t2. exfalso. admit. }
    subst cd cont inp0 gm0 dir t2.
    inversion TREECONT3. 2: { subst cd cont inp0 gm0 dir tcont. exfalso. admit. }
    subst cd cont inp0 gm0 dir tcont.
    inversion TREECONT4. subst inp0 gm0 dir tcont0.
    simpl tree_leaves. f_equal; f_equal.
    - subst inp. rewrite advance_input_inp_of_idx. 2: admit.
      rewrite advance_input_inp_of_idx. 2: admit.
      f_equal. lia.
    - apply GroupMap.MapS.Equal_eq.
      intro i'. destruct (PeanoNat.Nat.eq_dec i' i).
      + subst i'.
        unfold GroupMap.close. unfold GroupMap.open at 1.
        unfold GroupMap.find.
        rewrite GroupMap.Facts.add_eq_o. 2: reflexivity.
        subst inp. rewrite idx_inp_of_idx. 2: admit.
        rewrite advance_input_inp_of_idx. 2: admit.
        rewrite idx_inp_of_idx. 2: admit.
        replace (_ <=? _) with true. 2: { symmetry. apply PeanoNat.Nat.leb_le. lia. }
        rewrite GroupMap.Facts.add_eq_o. 2: reflexivity.
        rewrite GroupMap.Facts.add_eq_o. 2: reflexivity.
        f_equal. f_equal. f_equal. lia.
      + unfold GroupMap.close, GroupMap.add, GroupMap.open at 1, GroupMap.find.
        rewrite GroupMap.Facts.add_eq_o with (x := i) (y := i). 2: reflexivity.
        subst inp. rewrite advance_input_inp_of_idx, idx_inp_of_idx, idx_inp_of_idx by admit.
        replace (_ <=? _) with true. 2: { symmetry. apply PeanoNat.Nat.leb_le. lia. }
        rewrite GroupMap.Facts.add_neq_o. 2: auto.
        rewrite GroupMap.Facts.add_neq_o. 2: auto.
        unfold GroupMap.open. rewrite GroupMap.Facts.add_neq_o. 2: auto.
        reflexivity.
    - subst inp. rewrite advance_input_inp_of_idx. 2: admit.
      rewrite advance_input_inp_of_idx. 2: admit.
      f_equal. f_equal. lia.
  Admitted.

  Theorem theRegex_aux_spec:
    (* We perform backwards induction on i ∈ {1, ..., n+1}. *)
    forall np1_minus_i i, i = n + 1 - np1_minus_i ->
    (* Let i ∈ {1, ..., n+1}. *)
    i <> 0 -> i <= n + 1 ->
      (* Let gm be a valid group map... *)
      forall gm: group_map,
        wf_gm gm ->
        (* ... such that gm(i), gm(i+1), ..., gm(n) are undefined. *)
        (forall j, i <= j -> j <= n -> GroupMap.find j gm = None) ->
        forall inp qtail t,
          (* Let inp := inp(2(i-1))... *)
          inp = inp_of_idx (2*(i-1)) ->
          qtail = List.skipn (i-1) quants ->
          (* ... and t := T(R(i), inp, gm, →). *)
          is_tree rer [Areg (theRegex_aux q x_char semicolon_char i qtail)] inp gm forward t ->
          (* Then: *)
          (* - t has a leaf iff gm satisfies F_i *)
          (tree_leaves t gm inp forward <> [] <-> gm_satisfies_qbf_aux gm i qtail clauses = true) /\
          (* - for any leaf (inp', gm') of t, gm' and gm coincide on indices 1, 2, ..., i-1 *)
          (forall inp' gm', In (inp', gm') (tree_leaves t gm inp forward) ->
            forall j, 1 <= j -> j < i -> GroupMap.find j gm = GroupMap.find j gm') /\
          (* - if Q_i = ∃, then the first leaf of t maps i to (2*(i-1), 2(i-1)+1) iff gm[i ↦ (2(i-1), 2(i-1)+1)] satisfies F_{i+1}. *)
          (List.hd_error qtail = Some Qbf.Exists ->
          ((exists inpres gmres, tree_res t gm inp forward = Some (inpres, gmres) /\
          GroupMap.find i gmres = Some (GroupMap.Range (2*(i-1)) (Some (2*(i-1)+1)))) <->
          gm_satisfies_qbf_aux (GroupMap.add i (GroupMap.Range (2*(i-1)) (Some (2*(i-1)+1))) gm) (i+1) (List.tl qtail) clauses = true)).
  Proof.
    induction np1_minus_i.
    - intro i. rewrite Nat.sub_0_r. intros -> _ _ gm WF_gm _ inp qtail t.
      rewrite Nat.add_sub. intros EQ_inp EQ_qtail.
      unfold n, quants in EQ_qtail. rewrite skipn_all in EQ_qtail. subst qtail.
      simpl theRegex_aux. simpl gm_satisfies_qbf_aux. simpl hd_error.
      intro TREE. split; [|split; try discriminate].
      + apply check_conjunct_regex_spec with (inp := inp) (gm := gm) (t := t) (lflist := tree_leaves t gm inp forward); auto.
      + pose proof check_conjunct_regex_spec inp gm EQ_inp WF_gm t TREE _ eq_refl as SPEC.
        destruct SPEC as [SPEC _].
        intros inp' gm' IN. specialize (SPEC (inp', gm') IN).
        injection SPEC as -> ->. reflexivity.
    - intros i EQ_i i_INB _ gm WF_gm UNDEF inp qtail t EQ_inp EQ_qtail TREE.
      specialize (IHnp1_minus_i (S i)).
      specialize_prove IHnp1_minus_i. { rewrite EQ_i. lia. }
      specialize_prove IHnp1_minus_i by discriminate.
      specialize_prove IHnp1_minus_i. { rewrite EQ_i. lia. }
      assert (EQ'_qtail: qtail = List.nth (i-1) quants Qbf.Exists :: List.skipn i quants). {
        rewrite EQ_qtail. admit.
      }
      rewrite EQ'_qtail. rewrite EQ'_qtail in TREE.
      simpl gm_satisfies_qbf_aux.
      simpl theRegex_aux in TREE.
      destruct nth eqn:EQ_quant.
      + (* Exists *)
        inversion TREE. subst r1 r2 cont inp0 gm0 dir t0.
        rewrite app_nil_r in CONT. simpl in CONT.
        assert (exists tsub: tree, is_tree rer [Areg (def_var_regex x_char semicolon_char i)] inp gm forward tsub) as [tsub TREE_sub]. {
          eexists. apply compute_tr_is_tree.
        }
        pose proof leaves_concat rer inp gm forward [Areg (def_var_regex x_char semicolon_char i)] [Areg (theRegex_aux q x_char semicolon_char (S i) (skipn i quants))] t tsub CONT TREE_sub as CONCAT.
        pose proof def_var_regex_spec i inp i_INB ltac:(lia) EQ_inp tsub gm TREE_sub as DEF_SPEC.
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
        specialize_prove IHpos by admit.
        specialize_prove IHpos by admit.
        simpl "-" in IHpos, IHneg.
        specialize (IHpos (inp_of_idx (i + (i + 0))) (skipn i quants) t0).
        specialize_prove IHpos. { f_equal. lia. }
        specialize_prove IHpos. { rewrite Nat.sub_0_r. reflexivity. }
        specialize (IHpos ltac:(auto)).
        specialize (IHneg WF_gm).
        specialize_prove IHneg by admit.
        specialize (IHneg (inp_of_idx (i + (i + 0))) (skipn i quants) t1).
        specialize_prove IHneg. { f_equal. lia. }
        specialize_prove IHneg. { rewrite Nat.sub_0_r. reflexivity. }
        specialize (IHneg ltac:(auto)).
        assert (ly ++ ly0 <> [] <-> ly <> [] \/ ly0 <> []) by admit.
        rewrite H0. clear H0.
        rewrite H4 in IHpos. rewrite H5 in IHneg.
        rewrite orb_true_iff. split; [|split].
        * setoid_rewrite <- Heqgmpos. tauto.
        * intros inp' gm'. rewrite in_app_iff. intros [INl | INr].
          -- admit.
          -- admit.
        * admit.

      + (* Not exists *)
        inversion TREE.
        * (* Negative lookahead succeeds, i.e. QBF is valid, i.e. lookahead expression fails *)
          subst lk r1 cont inp0 gm0 dir t.
          inversion TREECONT. subst inp0 gm0 dir treecont.
          inversion TREELK. subst r1 r2 cont inp0 gm0 dir t.
          rewrite app_nil_r in CONT. simpl seq_list in CONT.
           admit.
        * (* Negative lookahead fails, i.e. QBF is invalid, i.e. lookahead expression doesn't fail *)
          admit.
  Admitted.
End Proofs.
