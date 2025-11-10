From JsRegexOptp Require Import RegexEncoding Qbf GroupMaps.
From Linden Require Import Parameters Chars Groups Semantics Tree.
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
      i < m -> List.nth_error clauses i = Some c ->
      inp = inp_of_idx (2*(n+i)) -> wf_gm gm ->
      forall t, is_tree rer [Areg (check_clause_regex x_char semicolon_char c)] inp gm forward t ->
        forall lflist, lflist = tree_leaves t gm inp forward ->
          (forall lf, In lf lflist -> lf = (inp_of_idx (2*(n+i+1)), gm)) /\
          (lflist <> nil <-> gm_satisfies_clause gm c = true).
  Proof.
    intros i c inp gm INB_i EQ_c EQ_inp WF_GM t TREE lflist EQ_lflist.
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
    assert (WF_c: wf_clause n c) by admit.
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

End Proofs.
