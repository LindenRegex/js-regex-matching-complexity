From JsRegexOptp Require Import RegexEncoding Qbf GroupMaps GroupMapQbfEquiv.
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

  Lemma concat_repeat_len {A: Type}:
    forall (l: list A) n, length (concat (repeat l n)) = length l * n.
  Proof.
    clear n. intros l n.
    rewrite concat_length, map_repeat, list_sum_repeat. apply Nat.mul_comm.
  Qed.

  Lemma str_len: length str = 2*(n+m).
  Proof.
    unfold str, theString.
    rewrite concat_repeat_len. reflexivity.
  Qed.

  Lemma rev_concat_repeat {A: Type}:
    forall (l: list A) i, rev (concat (repeat l i)) = concat (repeat (rev l) i).
  Proof.
    induction i.
    - reflexivity.
    - replace (S i) with (i + 1) at 1 by lia. simpl.
      rewrite repeat_app, concat_app, rev_app_distr. simpl.
      rewrite app_nil_r. congruence.
  Qed.

  Lemma inp_of_idx_even:
    forall i, i <= n + m ->
      inp_of_idx (2*i) = Input
        (List.concat (List.repeat [x_char; semicolon_char] (n+m-i)))
        (List.concat (List.repeat [semicolon_char; x_char] i)).
  Proof.
    induction i.
    - simpl. intros _. unfold inp_of_idx.
      rewrite Nat.sub_0_r. reflexivity.
    - intro LE. specialize (IHi ltac:(lia)).
      replace (2 * S i) with (2 + 2 * i) by lia.
      unfold inp_of_idx in *. injection IHi as IHnext IHprev.
      f_equal.
      + rewrite <- skipn_skipn. setoid_rewrite IHnext.
        replace (n + m - i) with (S (n + m - S i)) by lia. simpl. reflexivity.
      + rewrite PeanoNat.Nat.add_comm.
        apply (f_equal (rev (A := Character))) in IHprev. rewrite rev_involutive, rev_concat_repeat in IHprev.
        simpl in IHprev.
        rewrite <- firstn_skipn with (n := 2*i) (l := str).
        replace (2 * i) with (length (firstn (2 * i) str)) at 1. 2: {
          apply firstn_length_le. rewrite str_len. lia.
        }
        rewrite firstn_app_2. rewrite rev_app_distr.
        setoid_rewrite IHprev. rewrite rev_concat_repeat. simpl rev at 2.
        setoid_rewrite IHnext. replace (n + m - i) with (S (n + m - S i)) by lia.
        simpl. reflexivity.
  Qed.

  Lemma input_str_inp_of_idx:
    forall i, input_str (inp_of_idx i) = str.
  Proof.
    intro i. unfold input_str, inp_of_idx.
    rewrite rev_involutive. apply firstn_skipn.
  Qed.

  Lemma idx_inp_of_idx:
    forall i, i <= length str -> idx (inp_of_idx i) = i.
  Proof.
    intros i LE. unfold idx, inp_of_idx. rewrite rev_length.
    apply firstn_length_le. auto.
  Qed.

  Lemma advance_input_inp_of_idx:
    forall i, i < length str ->
      advance_input' (inp_of_idx i) forward = inp_of_idx (S i).
  Proof.
    intros i LT. unfold advance_input', advance_input, inp_of_idx.
    destruct (skipn i str) as [|h next] eqn:SKIPN.
    - exfalso. apply skipn_nil_length in SKIPN. lia.
    - f_equal.
      + rewrite <- skipn_skipn with (x := 1) (y := i). rewrite SKIPN. simpl. reflexivity.
      + rewrite <- firstn_skipn with (n := i) (l := str) at 2.
        replace (S i) with (i + 1) by lia.
        replace i with (length (firstn i str)) at 2. 2: {
          apply firstn_length_le. lia.
        }
        rewrite firstn_app_2. rewrite SKIPN, rev_app_distr. simpl. reflexivity.
  Qed.

  Lemma skipn_concat_repeat {A: Type}:
    forall (l: list A) n i,
      skipn (i * length l) (concat (repeat l n)) = concat (repeat l (n - i)).
  Proof.
    clear n. intros l n i. induction i.
    - rewrite Nat.sub_0_r. reflexivity.
    - destruct (Nat.lt_decidable i n).
      + replace (n - i) with (S (n - S i)) in IHi by lia.
        simpl in *.
        rewrite <- skipn_skipn, IHi, skipn_app, skipn_all, Nat.sub_diag. reflexivity.
      + replace (n - S i) with 0 by lia. simpl.
        rewrite skipn_all2. 2: {
          rewrite concat_repeat_len.
          rewrite (Nat.mul_comm (length l) n).
          change (length l + i * length l) with ((S i) * length l).
          apply Nat.mul_le_mono_r. lia.
        }
        reflexivity.
  Qed.

  Lemma substr_var:
    forall v, wf_var n v ->
      forall i, substr (inp_of_idx i) (2*(v-1)) (2*(v-1)+1) = [x_char].
  Proof.
    intros v WF_v i. unfold inp_of_idx, substr.
    replace (2*(v-1)+1-2*(v-1)) with 1 by lia.
    setoid_rewrite input_str_inp_of_idx.
    unfold wf_var in WF_v. assert (WF_v': v - 1 < n) by lia.
    unfold str, theString.
    rewrite (Nat.mul_comm 2 (v - 1)). change 2 with (length [x_char; semicolon_char]).
    rewrite skipn_concat_repeat.
    fold n m.
    destruct (n + m - (v - 1)) eqn:?; try lia. reflexivity.
  Qed.

  Lemma advance_input'_n:
    forall inp dir, advance_input_n inp 1 dir = advance_input' inp dir.
  Proof.
    intros [next pref] []; unfold advance_input'; simpl.
    - destruct next as [|x next]; simpl; reflexivity.
    - destruct pref as [|x pref]; simpl; reflexivity.
  Qed.

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
    rewrite substr_var. 2: auto.
    destruct (m-i) eqn:?; try lia. rewrite advance_input'_n, advance_input_inp_of_idx. simpl.
    rewrite EqDec.reflb. f_equal. f_equal. f_equal. lia. rewrite str_len. lia.
  Qed.

  Lemma read_backref_var_unsat:
    forall (gm: group_map) (v: variable) (i: nat),
      i < m -> wf_gm gm ->
      gm_satisfies_var gm v = false -> read_backref rer gm v (inp_of_idx (2*(n+i))) forward = Some ([], inp_of_idx (2*(n+i))).
  Proof.
    intros gm v i INB_i WF_GM UNSAT. unfold gm_satisfies_var in UNSAT.
    unfold read_backref. destruct GroupMap.find; try discriminate. reflexivity.
  Qed.


  (* Lemma specifying the behavior of the regex checking a literal (either \i or \i x).*)
  Lemma check_literal_regex_spec:
    (* Let lit be a well-formed literal and gm be a valid group map. *)
    forall (i: nat) (lit: literal) (inp: input) (gm: group_map),
      i < m -> wf_literal n lit ->
      inp = inp_of_idx (2*(n+i)) -> wf_gm gm ->
      (* Let t be the tree of r_lit with input inp(2*(n+i)) for some 0 ≤ i < m and group map gm. *)
      forall t, is_tree rer [Areg (check_literal_regex x_char lit)] inp gm forward t ->
        forall lflist, lflist = tree_leaves t gm inp forward ->
          (* Then: *)
          (* - if gm satisfies lit, then t has exactly one leaf, (inp(2*(n+i)+1), gm), *)
          (gm_satisfies_lit gm lit = true -> lflist = [(inp_of_idx (2*(n+i)+1), gm)]) /\
          (* - otherwise, t has either no leaf or exactly one leaf, (inp(2*(n+i)), gm). *)
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

  (* Lemma specifying the behavior of the regex checking the validity of a clause, without the separator. *)
  Lemma check_clause_regex_aux_spec:
    (* Let r be the regex checking the validity of a well-formed clause c, gm a valid group map and 0 <= i < m. *)
    forall (i: nat) (c: clause) (inp: input) (gm: group_map),
      i < m -> wf_clause n c ->
      inp = inp_of_idx (2*(n+i)) -> wf_gm gm ->
      (* Let t be the tree of r with input inp(2*(n+i)) and group map gm. *)
      forall t, is_tree rer [Areg (check_clause_regex_aux x_char c)] inp gm forward t ->
        forall lflist, lflist = tree_leaves t gm inp forward ->
          (* Then: *)
          (* - all the leaves of lf are either (inp(2*(n+i)+1), gm) or (inp(2*(n+i)), gm), *)
          (forall lf, In lf lflist -> lf = (inp_of_idx (2*(n+i)+1), gm) \/ lf = (inp, gm)) /\
          (* - lf contains a leaf (inp(2*(n+i)+1), gm) iff gm satisfies c. *)
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

  (* Lemma specifying the behavior of the regex that checks a clause. *)
  Lemma check_clause_regex_spec:
    (* Let r be the regex checking the validity of a well-formed clause c, gm a valid group map, and 0 <= i < m. *)
    forall (i: nat) (c: clause) (inp: input) (gm: group_map),
      i < m -> wf_clause n c ->
      inp = inp_of_idx (2*(n+i)) -> wf_gm gm ->
      (* Let t be the tree of r on input inp(2*(n+i)) and group map gm. *)
      forall t, is_tree rer [Areg (check_clause_regex x_char semicolon_char c)] inp gm forward t ->
        forall lflist, lflist = tree_leaves t gm inp forward ->
          (* Then: *)
          (* - all the leaves of t, if any, are equal to (inp(2*(n+i+1)), gm), *)
          (forall lf, In lf lflist -> lf = (inp_of_idx (2*(n+i+1)), gm)) /\
          (* - t has (at least) a leaf iff gm satisfies c. *)
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

  (* Lemma specifying the behavior of the regex checking the conjunction of clauses. *)
  Lemma check_conjunct_regex_spec:
    (* Let r be the regex checking the validity of the conjunction of clauses, and gm a valid group map. *)
    forall (inp: input) (gm: group_map),
      inp = inp_of_idx (2*n) -> wf_gm gm ->
      (* Let t be the tree of r on input inp(2*n) and group map gm. *)
      forall t, is_tree rer [Areg (check_conjunct_regex x_char semicolon_char (rev clauses))] inp gm forward t ->
        forall lflist, lflist = tree_leaves t gm inp forward ->
          (* Then: *)
          (* - all the leaves of t (if any) are equal to (inp(2*(n+m)), gm), *)
          (forall lf, In lf lflist -> lf = (inp_of_idx (2*(n+m)), gm)) /\
          (* - t has (at least) a leaf iff gm satisfies the conjunction of clauses. *)
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

  (* Lemma specifying the behavior of the regex that defines a variable. *)
  Lemma def_var_regex_spec:
    (* Let 0 < i <= n be a variable and r be the regex that defines variable i, and gm a group map (not necessarily valid). *)
    forall (i: nat) (inp: input),
      i <> 0 -> i <= n -> inp = inp_of_idx (2*(i-1)) ->
      forall (t: tree) (gm: group_map),
        (* Let t be the tree of r on input inp(2*(i-1)) and group map gm. *)
        is_tree rer [Areg (def_var_regex x_char semicolon_char i)] inp gm forward t ->
        (* Then t has two leaves: *)
        tree_leaves t gm inp forward = [
          (* - (inp(2*i), gm.add(i, range(i))), *)
          (inp_of_idx (2*i), GroupMap.add i (GroupMap.Range (2*(i-1)) (Some (2*(i-1)+1))) gm);
          (* - (inp(2*i), gm). *)
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

  Lemma negb_true_iff_not_true:
    forall b: bool, negb b = true <-> ~(b = true).
  Proof.
    intros []; simpl; split.
    - discriminate.
    - contradiction.
    - discriminate.
    - reflexivity.
  Qed.

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
          -- destruct IHpos as [_ [IHpos _]]. intros j ? ?. transitivity (GroupMap.find j gmpos).
             ++ rewrite Heqgmpos. unfold GroupMap.find, GroupMap.add.
                symmetry. apply GroupMap.Facts.add_neq_o. lia.
             ++ apply IHpos with (inp' := inp'); auto.
          -- destruct IHneg as [_ [IHneg _]]. intros j ? ?.
             apply IHneg with (inp' := inp'); auto.
        * simpl hd_error. intros _.
          rewrite first_tree_leaf, <- H.
          subst lmapped.
          destruct ly as [|[inpres gmres] ly].
          -- (* No result on left: prove False <-> False *)
             transitivity False.
             ++ split; try contradiction. simpl. rewrite app_nil_r.
                intros [inpres [gmres [? ?]]].
                destruct IHneg as [_ [IHneg _]].
                specialize (IHneg inpres gmres).
                specialize_prove IHneg. {
                  destruct ly0; try discriminate. injection H0 as ->. left. reflexivity.
                }
                specialize (IHneg i).
                do 2 specialize_prove IHneg by lia.
                rewrite <- IHneg in H1.
                rewrite UNDEF in H1 by lia. discriminate.
             ++ split; try contradiction. destruct IHpos as [IHpos _].
                intro. setoid_rewrite <- Heqgmpos in H0.
                replace (i+1) with (S i) in H0 by lia.
                rewrite <- IHpos in H0. contradiction.
          -- (* A result on left: prove True <-> True *)
             transitivity True; split; intro; try solve[split].
             ++ simpl. exists inpres. exists gmres.
                split; try reflexivity.
                destruct IHpos as [_ [IHpos _]].
                specialize (IHpos inpres gmres ltac:(left; reflexivity)).
                specialize (IHpos i ltac:(lia) ltac:(lia)).
                rewrite <- IHpos. rewrite Heqgmpos.
                unfold GroupMap.find, GroupMap.add.
                rewrite GroupMap.Facts.add_eq_o by reflexivity. reflexivity.
             ++ setoid_rewrite <- Heqgmpos. destruct IHpos as [IHpos _].
                replace (i+1) with (S i) by lia. apply IHpos. discriminate.

      + (* Not exists *)
        inversion TREE.
        * (* Negative lookahead succeeds, i.e. QBF is valid, i.e. lookahead expression fails *)
          subst lk r1 cont inp0 gm0 dir t.
          inversion TREECONT. subst inp0 gm0 dir treecont.
          inversion TREELK. subst r1 r2 cont inp0 gm0 dir t.
          rewrite app_nil_r in CONT. simpl seq_list in CONT.
          assert (exists treelksub: tree, is_tree rer [Areg (def_var_regex x_char semicolon_char i)] inp gm forward treelksub). { eexists; apply compute_tr_is_tree. }
          destruct H as [treelksub TREELKSUB].
          pose proof leaves_concat rer inp gm forward [Areg (def_var_regex x_char semicolon_char i)] [Areg (theRegex_aux q x_char semicolon_char (S i) (skipn i quants))] treelk treelksub CONT TREELKSUB as CONCAT.
          pose proof def_var_regex_spec i inp ltac:(auto) ltac:(lia) EQ_inp treelksub gm TREELKSUB as DEF_SPEC.
          remember (GroupMap.add i (GroupMap.Range (2*(i-1)) (Some (2*(i-1)+1))) gm) as gmpos.
          rewrite DEF_SPEC in CONCAT.
          inversion CONCAT. subst x lbase f.
          inversion FM. subst x lbase f.
          inversion FM0. subst f lmapped0 lmapped.
          inversion HEAD. subst act dir l. simpl in H3, TREE0.
          inversion HEAD0. subst act dir l. simpl in TREE1, H4.
          unfold lk_result in RES_LK. simpl in RES_LK. rewrite first_tree_leaf in RES_LK.
          assert (tree_leaves treelk gm inp forward = []). {
            destruct (tree_leaves treelk gm inp forward); try discriminate. reflexivity.
          }
          rewrite <- H in H0.
          replace ly with (nil (A := leaf)) in *. 2: { destruct ly; try discriminate; reflexivity. }
          replace ly0 with (nil (A := leaf)) in *. 2: { destruct ly0; try discriminate; reflexivity. }
          simpl. rewrite <- H. simpl in *.
          pose proof (IHnp1_minus_i gmpos) as IHpos.
          pose proof (IHnp1_minus_i gm) as IHneg.
          specialize_prove IHpos by admit.
          specialize_prove IHpos by admit.
          simpl "-" in IHpos, IHneg.
          specialize (IHpos (inp_of_idx (i + (i + 0))) (skipn i quants) t).
          specialize_prove IHpos. { f_equal. lia. }
          specialize_prove IHpos. { rewrite Nat.sub_0_r. reflexivity. }
          specialize (IHpos ltac:(auto)).
          specialize (IHneg WF_gm).
          specialize_prove IHneg by admit.
          specialize (IHneg (inp_of_idx (i + (i + 0))) (skipn i quants) t0).
          specialize_prove IHneg. { f_equal. lia. }
          specialize_prove IHneg. { rewrite Nat.sub_0_r. reflexivity. }
          specialize (IHneg ltac:(auto)).
          rewrite H3 in IHpos. rewrite H4 in IHneg.
          split; [|split]; try discriminate.
          -- split; try discriminate. intros _. apply andb_true_intro. do 2 rewrite negb_true_iff_not_true. setoid_rewrite <- Heqgmpos. tauto.
          -- intros inp' gm' []; try contradiction. injection H1 as <- <-. reflexivity.
        * (* Negative lookahead fails, i.e. QBF is invalid, i.e. lookahead expression doesn't fail *)
          subst lk r1 cont inp0 gm0 dir t.
          simpl.
          inversion TREELK. subst r1 r2 cont inp0 gm0 dir t.
          simpl seq_list in CONT. rewrite app_nil_r in CONT.
          assert (exists treelksub: tree, is_tree rer [Areg (def_var_regex x_char semicolon_char i)] inp gm forward treelksub). { eexists; apply compute_tr_is_tree. }
          destruct H as [treelksub TREELKSUB].
          pose proof leaves_concat rer inp gm forward [Areg (def_var_regex x_char semicolon_char i)] [Areg (theRegex_aux q x_char semicolon_char (S i) (skipn i quants))] treelk treelksub CONT TREELKSUB as CONCAT.
          pose proof def_var_regex_spec i inp ltac:(auto) ltac:(lia) EQ_inp treelksub gm TREELKSUB as DEF_SPEC.
          remember (GroupMap.add i (GroupMap.Range (2*(i-1)) (Some (2*(i-1)+1))) gm) as gmpos.
          rewrite DEF_SPEC in CONCAT.
          inversion CONCAT. subst x lbase f.
          inversion FM. subst x lbase f.
          inversion FM0. subst f lmapped0 lmapped.
          inversion HEAD. subst act dir l. simpl in H3, TREE0.
          inversion HEAD0. subst act dir l. simpl in TREE1, H4.
          unfold lk_result in FAIL_LK. simpl in FAIL_LK. rewrite first_tree_leaf in FAIL_LK.
          assert (tree_leaves treelk gm inp forward <> []). {
            destruct (tree_leaves treelk gm inp forward); discriminate.
          }
          rewrite <- H in H0. assert (ly <> [] \/ ly0 <> []) by admit.
          pose proof (IHnp1_minus_i gmpos) as IHpos.
          pose proof (IHnp1_minus_i gm) as IHneg.
          specialize_prove IHpos by admit.
          specialize_prove IHpos by admit.
          simpl "-" in IHpos, IHneg.
          specialize (IHpos (inp_of_idx (i + (i + 0))) (skipn i quants) t).
          specialize_prove IHpos. { f_equal. lia. }
          specialize_prove IHpos. { rewrite Nat.sub_0_r. reflexivity. }
          specialize (IHpos ltac:(auto)).
          specialize (IHneg WF_gm).
          specialize_prove IHneg by admit.
          specialize (IHneg (inp_of_idx (i + (i + 0))) (skipn i quants) t0).
          specialize_prove IHneg. { f_equal. lia. }
          specialize_prove IHneg. { rewrite Nat.sub_0_r. reflexivity. }
          specialize (IHneg ltac:(auto)).
          rewrite H3 in IHpos. rewrite H4 in IHneg.
          split; [|split]; try discriminate.
          -- split; try contradiction; intro.
             exfalso. apply andb_true_iff in H2.
             do 2 rewrite negb_true_iff_not_true in H2. setoid_rewrite <- Heqgmpos in H2.
             tauto.
          -- contradiction.
  Admitted.



  Definition regex_matches_string (rer: RegExpRecord) (r: regex) (s: LWParameters.string): Prop :=
    forall t: tree, is_tree rer [Areg r] (init_input s) GroupMap.empty forward t ->
      first_leaf t (init_input s) <> None.

  Lemma emptygm_find: forall i, GroupMap.find i GroupMap.empty = None.
  Proof.
    intro i. unfold GroupMap.find, GroupMap.empty.
    apply GroupMap.Facts.empty_o.
  Qed.

  Lemma emptygm_wf: wf_gm GroupMap.empty.
  Proof.
    unfold wf_gm. intro gid. left. apply emptygm_find. 
  Qed.
  

  Theorem qbf_regex:
    regex_matches_string rer (theRegex q x_char semicolon_char) str <->
    qbf_valid q = true.
  Proof.
    pose proof theRegex_aux_spec n 1 ltac:(lia) ltac:(lia) ltac:(lia) GroupMap.empty ltac:(apply emptygm_wf).
    specialize_prove H. {
      intros j _ _. apply emptygm_find.
    }
    specialize (H (inp_of_idx 0) quants).
    split.
    - intro MATCHES. unfold regex_matches_string in MATCHES.
      assert (exists t: tree, is_tree rer [Areg (theRegex q x_char semicolon_char)] (init_input str) GroupMap.empty forward t) as [t TREE]. {
        eexists. apply compute_tr_is_tree.
      }
      specialize (MATCHES t TREE).
      specialize (H t eq_refl eq_refl TREE).
      destruct H as [H _].
      unfold quants, clauses in H.
      rewrite equiv_gm_env_valid with (q := q) in H.
      apply H. setoid_rewrite first_tree_leaf in MATCHES.
      rewrite hd_error_none_nil in MATCHES. auto.
    - intro VALID. unfold regex_matches_string.
      intros t TREE.
      specialize (H t eq_refl eq_refl TREE).
      destruct H as [H _].
      setoid_rewrite first_tree_leaf. rewrite hd_error_none_nil.
      apply H. unfold quants, clauses. rewrite equiv_gm_env_valid. auto.
  Qed.
End Proofs.
