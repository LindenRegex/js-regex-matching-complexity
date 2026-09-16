From Linden Require Import Regex Parameters Semantics Chars StrictSuffix
  FunctionalSemantics Tactics Tree FunctionalUtils ComputeIsTree
  Semantics.Tree Semantics.Groups.
From JsRegexOptp Require Export Basics.
From Warblre Require Import Base spec.RegExpRecord.
From Stdlib Require Import List Sorted Lia.
Import ListNotations.

Section ComputeResult.

  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).

  Inductive match_result :=
  | Out_of_fuel: match_result
  | NoMatch: match_result
  | Success: leaf -> match_result.

  Fixpoint compute_result (act: actions) (inp: input) (gm: group_map) (dir: Direction) (fuel:nat): match_result :=
    match fuel with
    | 0 => Out_of_fuel
    | S fuel =>
        match act with
        | [] => Success (inp, gm)
        | Acheck strcheck :: cont =>
            if (is_strict_suffix inp strcheck dir) then
              compute_result cont inp gm dir fuel
            else NoMatch
        | Aclose gid :: cont =>
            compute_result cont inp (GroupMap.close (idx inp) gid gm) dir fuel
        | Areg Epsilon::cont => compute_result cont inp gm dir fuel
        | Areg (Regex.Character cd)::cont =>
            match read_char rer cd inp dir with
            | Some (c, nextinp) =>
                compute_result cont nextinp gm dir fuel
            | None => NoMatch
            end
        (* tree_disj *)
        | Areg (Disjunction r1 r2)::cont =>
            match compute_result (Areg r1 :: cont) inp gm dir fuel with
            | Out_of_fuel => Out_of_fuel
            | Success lf => Success lf
            | NoMatch => compute_result (Areg r2 :: cont) inp gm dir fuel
            end
        | Areg (Sequence r1 r2)::cont =>
            compute_result (seq_list r1 r2 dir ++ cont) inp gm dir fuel
        (* tree_quant_forced *)
        | Areg (Quantified greedy (S min) delta r1)::cont =>
            let gidl := def_groups r1 in
            compute_result (Areg r1 :: Areg (Quantified greedy min delta r1) :: cont) inp (GroupMap.reset gidl gm) dir fuel
        (* tree_quant_done *)
        | Areg (Quantified greedy 0 (NoI.N 0) r1)::cont =>
            compute_result cont inp gm dir fuel
        (* tree_quant_free *)
        | Areg (Quantified greedy 0 delta r1)::cont =>
            let gidl := def_groups r1 in
            match greedy with
            | true =>
                match (compute_result (Areg r1 :: Acheck inp :: Areg (Quantified greedy 0 (noi_pred delta) r1) :: cont) inp (GroupMap.reset gidl gm) dir fuel) with
                | Out_of_fuel => Out_of_fuel
                | Success lf => Success lf
                | NoMatch => compute_result cont inp gm dir fuel
                end
            | false =>
                match (compute_result cont inp gm dir fuel) with
                | Out_of_fuel => Out_of_fuel
                | Success lf => Success lf
                | NoMatch => (compute_result (Areg r1 :: Acheck inp :: Areg (Quantified greedy 0 (noi_pred delta) r1) :: cont) inp (GroupMap.reset gidl gm) dir fuel)
                end
            end
        | Areg (Group gid r1)::cont =>
            compute_result (Areg r1 :: Aclose gid :: cont) inp (GroupMap.open (idx inp) gid gm) dir fuel
        (* tree_lk, tree_lk_fail *)
        | Areg (Lookaround lk r1)::cont =>
            match (compute_result [Areg r1] inp gm (lk_dir lk) fuel) with
            | Out_of_fuel => Out_of_fuel
            | Success (_,gmlk) =>
                match (positivity lk) with
                | false => NoMatch
                | true => compute_result cont inp gmlk dir fuel
                end
            | NoMatch =>
                match (positivity lk) with
                | true => NoMatch
                | false => compute_result cont inp gm dir fuel
                end
            end
        | Areg (Anchor a)::cont =>
            if anchor_satisfied rer a inp then
              compute_result cont inp gm dir fuel
            else NoMatch
        | Areg (Backreference gid)::cont =>
          match read_backref rer gm gid inp dir with
          | Some (br_str, nextinp) =>
            compute_result cont nextinp gm dir fuel
          | None => NoMatch
          end
        end
    end.

  Definition res_to_leaf (mr:match_result) : option (option leaf) :=
    match mr with
    | Out_of_fuel => None
    | NoMatch => Some None
    | Success leaf => Some (Some leaf)
    end.

  Lemma destruct_delta:
    forall d, d = NoI.N 0 \/ (exists del, d = (NoI.N 1 + del)%NoI).
  Proof.
    intros d. destruct d; auto.
    - destruct n; eauto. right. exists (NoI.N n). auto.
    - right. exists NoI.Inf. auto.
  Qed.

  Lemma simpl_delta_match:
    forall X (x y:X) pred,
      (match (NoI.N 1 + pred)%NoI with
       | NoI.N 0 => x
       | _ => y end) = y.
  Proof. intros X x y pred. destruct pred; simpl; auto. Qed.

  Lemma simpl_pred:
    forall pred, noi_pred (NoI.N 1 + pred)%NoI = pred.
  Proof. intros. destruct pred; simpl; auto. rewrite PeanoNat.Nat.sub_0_r. auto. Qed.

  Lemma compute_result_is_tree:
    forall fuel act inp gm dir leaf,
      res_to_leaf (compute_result act inp gm dir fuel) = Some leaf ->
      exists t, is_tree rer act inp gm dir t /\
             tree_res t gm inp dir = leaf.
  Proof.
    intros fuel. induction fuel; intros.
    { simpl in H. inversion H. }
    simpl in H. destruct act.
    { simpl in H. simpl. eexists. split; eauto. constructor. inversion H. auto. }
    destruct a.
    2:{ destruct is_strict_suffix eqn:ISS.
        - apply IHfuel in H as [t [CT LF]]. eexists. split.
          + constructor. apply is_strict_suffix_correct. auto. eauto. + auto.
        - simpl in H. inversion H. eexists. split.
          + apply tree_check_fail. rewrite <- is_strict_suffix_correct.
            rewrite ISS. auto. + auto. }
    2:{ apply IHfuel in H as [t [CT LF]]. eexists; split.
        + constructor. eauto. + auto. }
    destruct r.
    - apply IHfuel in H as [t [CT LF]]. eexists. split.
      + constructor. apply CT. + auto.
    - destruct read_char eqn:READ.
      + destruct p. apply IHfuel in H as [t' [CT LF]]. eexists. split.
        * eapply tree_char; eauto.
        * simpl. apply read_char_success_advance in READ. apply advance_input_success in READ.
          subst. auto.
      + eexists. split.
        * constructor. auto.
        * simpl. simpl in H. inversion H. auto.
    - destruct compute_result eqn:CR1.
      + inversion H.
      + apply f_equal with (f:=res_to_leaf) in CR1.
        apply IHfuel in CR1 as [t1 [CT1 LF1]].
        apply IHfuel in H as [t2 [CT2 LF2]]. eexists; split.
        * constructor; eauto.
        * simpl. rewrite LF1. simpl. auto.
      + apply f_equal with (f:=res_to_leaf) in CR1.
        apply IHfuel in CR1 as [t1 [CT1 LF1]].
        (* we need productivity to guess what the tree of the second branch is *)
        specialize (is_tree_productivity rer (Areg r2::act) inp gm dir) as [t IT].
        eexists. split.
        * constructor; eauto.
        * simpl. rewrite LF1. simpl. inversion H. auto.
    - simpl in H. apply IHfuel in H as [t [CT LF]].
      eexists. split; eauto. constructor; auto.
    - destruct min.
      (* forced *)
      2:{ apply IHfuel in H as [t [CT LF]]. eexists. split; eauto.
          constructor; eauto. auto. }
      specialize (destruct_delta delta) as [DONE|[pred FREE]]; subst.
      (* done *)
      { apply IHfuel in H as [t [CT LF]]. eexists. split; eauto.
        constructor. auto. }
      (* free *)
      destruct greedy.
      + (* we need productivity to guess what the tree of the untaken branch is *)
        specialize (is_tree_productivity rer act inp gm dir) as [tskip ITskip].
        rewrite simpl_delta_match in H. rewrite simpl_pred in H.
        destruct compute_result eqn:CR; try solve[inversion H].
        * clear ITskip. apply IHfuel in H as [ts [CTs LFs]].
          apply f_equal with (f:=res_to_leaf) in CR.
          apply IHfuel in CR as [t [CT LF]]. eexists. split.
          ** eapply tree_quant_free; eauto.
          ** simpl. rewrite LF. simpl. auto.
        * apply f_equal with (f:=res_to_leaf) in CR.
          apply IHfuel in CR as [t [CT LF]]. eexists. split.
          ** eapply tree_quant_free; eauto.
          ** simpl. rewrite LF. simpl. inversion H. auto.
      + (* we need productivity to guess what the tree of the untaken branch is *)
        specialize (is_tree_productivity rer (Areg r :: Acheck inp :: Areg (Quantified false 0 pred r)::act) inp (GroupMap.reset (def_groups r) gm) dir) as [titer ITiter].
        rewrite simpl_delta_match in H. rewrite simpl_pred in H.
        destruct compute_result eqn:CR; try solve[inversion H].
        * clear ITiter. apply IHfuel in H as [ts [CTs LFs]].
          apply f_equal with (f:=res_to_leaf) in CR.
          apply IHfuel in CR as [t [CT LF]]. eexists. split.
          ** eapply tree_quant_free; eauto.
          ** simpl. rewrite LF. simpl. auto.
        * apply f_equal with (f:=res_to_leaf) in CR.
          apply IHfuel in CR as [t [CT LF]]. eexists. split.
          ** eapply tree_quant_free; eauto.
          ** simpl. rewrite LF. simpl. inversion H. auto.
    - destruct compute_result eqn:CR; try solve[inversion H].
      + apply f_equal with (f:=res_to_leaf) in CR.
        apply IHfuel in CR as [t [CT LF]].
        destruct positivity eqn:POS.
        * eexists. split.
          ** eapply tree_lk_fail; eauto. unfold lk_result. rewrite POS, LF. auto.
          ** inversion H. auto.
        * apply IHfuel in H as [ta [CTa LFa]].
          eexists. split.
          ** eapply tree_lk; eauto. unfold lk_result. rewrite POS, LF. auto.
          ** simpl. rewrite POS, LF. auto.
      + destruct l. apply f_equal with (f:=res_to_leaf) in CR.
        apply IHfuel in CR as [t [CT LF]].
        destruct positivity eqn:POS.
        * apply IHfuel in H as [ta [CTa LFa]].
          eexists. split.
          ** eapply tree_lk; eauto. unfold lk_result. rewrite POS, LF. auto.
          ** simpl. rewrite POS, LF. auto.
        * eexists. split.
          ** eapply tree_lk_fail; eauto. unfold lk_result. rewrite POS, LF. auto.
          ** inversion H. auto.
    - apply IHfuel in H as [t [CT LF]]. eexists. split.
      + constructor. eauto. + auto.
    - destruct anchor_satisfied eqn:ANC.
      + apply IHfuel in H as [t [CT LF]]. eexists. split.
        * constructor; eauto. * auto.
      + eexists. split.
        * apply tree_anchor_fail. auto. * inversion H. auto.
    - destruct read_backref eqn:BACK.
      + destruct p. apply IHfuel in H as [t [CT LF]]. eexists. split.
        * eapply tree_backref; eauto.
        * apply read_backref_success_advance in BACK. subst. auto.
      + eexists. split.
        * apply tree_backref_fail. auto. * inversion H. auto.
Qed.

End ComputeResult.

Section MembershipProof.
  Context {params: LindenParameters}.

  (* Formalizing when an input, list of actions and direction come from a supported regex *)
  Inductive act_from_regex (r: regex): input -> actions -> Direction -> Prop :=
  | afr_refl: forall inp dir, act_from_regex r inp [Areg r] dir
  | afr_pop_check: forall inp inpcheck l dir,
      strict_suffix inp inpcheck dir ->
      act_from_regex r inp (Acheck inpcheck :: l) dir ->
      act_from_regex r inp l dir
  | afr_pop_close: forall inp gid l dir,
      act_from_regex r inp (Aclose gid :: l) dir -> act_from_regex r inp l dir
  | afr_pop_epsilon: forall inp l dir,
      act_from_regex r inp (Areg Epsilon :: l) dir -> act_from_regex r inp l dir
  | afr_pop_char: forall inp nextinp cd l dir,
      act_from_regex r inp (Areg (Regex.Character cd) :: l) dir ->
      advance_input inp dir = Some nextinp ->
      act_from_regex r nextinp l dir
  | afr_pop_disj_l: forall inp r1 r2 l dir,
      act_from_regex r inp (Areg (Disjunction r1 r2) :: l) dir ->
      act_from_regex r inp (Areg r1 :: l) dir
  | afr_pop_disj_r: forall inp r1 r2 l dir,
      act_from_regex r inp (Areg (Disjunction r1 r2) :: l) dir ->
      act_from_regex r inp (Areg r2 :: l) dir
  | afr_pop_sequence: forall inp r1 r2 l dir,
      act_from_regex r inp (Areg (Sequence r1 r2) :: l) dir ->
      act_from_regex r inp (seq_list r1 r2 dir ++ l) dir
  | afr_pop_quant_done: forall inp greedy r1 l dir,
      act_from_regex r inp (Areg (Quantified greedy 0 (NoI.N 0) r1) :: l) dir ->
      act_from_regex r inp l dir
  | afr_pop_quant_forced: forall inp greedy min delta r1 l dir,
      act_from_regex r inp (Areg (Quantified greedy (S min) delta r1) :: l) dir ->
      act_from_regex r inp (Areg r1 :: Areg (Quantified greedy min delta r1) :: l) dir
  | afr_pop_quant_free_iter: forall greedy delta r1 inp l dir,
      act_from_regex r inp (Areg (Quantified greedy 0 (NoI.N 1 + delta)%NoI r1) :: l) dir ->
      act_from_regex r inp (Areg r1 :: Acheck inp :: Areg (Quantified greedy 0 delta r1) :: l) dir
  | afr_pop_quant_free_skip: forall inp greedy delta r1 l dir,
      act_from_regex r inp (Areg (Quantified greedy 0 (NoI.N 1 + delta)%NoI r1) :: l) dir ->
      act_from_regex r inp l dir
  | afr_pop_group: forall inp gid r1 l dir,
      act_from_regex r inp (Areg (Group gid r1) :: l) dir ->
      act_from_regex r inp (Areg r1 :: Aclose gid :: l) dir
  | afr_pop_lk_lk: forall inp lk rlk l dir,
      act_from_regex r inp (Areg (Lookaround lk rlk) :: l) dir ->
      act_from_regex r inp [Areg rlk] (lk_dir lk)
  | afr_pop_lk_cont: forall inp lk rlk l dir,
      act_from_regex r inp (Areg (Lookaround lk rlk) :: l) dir ->
      act_from_regex r inp l dir
  | afr_pop_anchor: forall inp a l dir,
      act_from_regex r inp (Areg (Anchor a) :: l) dir ->
      act_from_regex r inp l dir
  | afr_pop_backref: forall inp n nextinp gid l dir,
      act_from_regex r inp (Areg (Backreference gid) :: l) dir ->
      advance_input_n inp n dir = nextinp ->
      act_from_regex r nextinp l dir.

  (** * In a valid list of actions, all checks are ordered (non-strictly) from more to less restrictive. *)

  Definition input_le (dir: Direction) (inp1 inp2: input): Prop :=
    inp1 = inp2 \/ strict_suffix inp1 inp2 dir.

  Lemma input_le_refl: forall dir, Relations_1.Reflexive input (input_le dir).
  Proof.
    unfold Relations_1.Reflexive. intros dir x. left. reflexivity.
  Qed.

  Lemma input_le_trans: forall dir, Relations_1.Transitive (input_le dir).
  Proof.
    unfold Relations_1.Transitive. intros dir x y z XY YZ.
    destruct XY as [-> | XY]; destruct YZ as [-> | YZ].
    - apply input_le_refl.
    - right. auto.
    - right. auto.
    - right. eapply strict_suffix_trans; eauto.
  Qed.

  #[global] Add Parametric Relation (dir: Direction): input (input_le dir)
    reflexivity proved by (input_le_refl dir)
    transitivity proved by (input_le_trans dir)
    as input_le_rel.

  Fixpoint actions_checks (act: actions): list input :=
    match act with
    | [] => []
    | Acheck inpcheck :: q => inpcheck :: actions_checks q
    | _ :: q => actions_checks q
    end.

  Lemma afr_checks_ordered:
    forall r inp act dir,
      act_from_regex r inp act dir -> Sorted (input_le dir) (inp :: actions_checks act).
  Proof.
    induction 1; try solve[simpl in IHact_from_regex; auto].
    - simpl. constructor; constructor.
    - simpl in IHact_from_regex. constructor.
      + inversion IHact_from_regex. subst a l0. inversion H3. auto.
      + apply Sorted_StronglySorted in IHact_from_regex. 2: apply input_le_trans.
        inversion IHact_from_regex. subst a l0.
        destruct (actions_checks l) as [ | inpcheck' q]; constructor.
        inversion H4. subst x l0. inversion H6. auto.
    - simpl in IHact_from_regex. inversion IHact_from_regex. subst a l0. constructor; auto.
      destruct actions_checks as [|inpcheck q]; constructor.
      inversion H4. subst b l0. transitivity inp; auto.
      right. apply read_suffix. auto.
    - simpl in *. inversion IHact_from_regex. subst a l0. constructor; destruct dir; simpl; auto.
    - simpl in *. constructor; auto.
      constructor. reflexivity.
    - simpl in *. inversion IHact_from_regex. subst a l0. constructor; auto.
      destruct actions_checks as [|inpcheck q]; constructor.
      inversion H4. subst b l0. transitivity inp; auto.
      apply advance_input_n_suffix with (n := n). congruence.
  Qed.


  (** * In a valid list of actions, a check is always followed by a quantifier with a minimum number of repetitions equal to zero. *)
  Definition checks_fby_quant (act: actions) :=
    forall (i: nat) (inpcheck: input),
      List.nth_error act i = Some (Acheck inpcheck) ->
      exists greedy delta r,
        List.nth_error act (S i) = Some (Areg (Quantified greedy 0 delta r)).

  Lemma afr_checks_fby_quant:
    forall r inp act dir, act_from_regex r inp act dir -> checks_fby_quant act.
  Proof.
    induction 1; unfold checks_fby_quant; try solve[
      intros i inpcheck0 EQ_CHECK;
      specialize (IHact_from_regex (S i) inpcheck0 EQ_CHECK);auto
    ].
    - intros i inpcheck. destruct i; try discriminate.
      simpl. destruct i; discriminate.
    - intros i inpcheck EQ_CHECK. destruct i; try discriminate.
      specialize (IHact_from_regex (S i) inpcheck EQ_CHECK). auto.
    - intros i inpcheck EQ_CHECK. destruct i; try discriminate.
      specialize (IHact_from_regex (S i) inpcheck EQ_CHECK). auto.
    - intros i inpcheck EQ_CHECK. destruct dir; destruct i as [ | []]; try discriminate;
        specialize (IHact_from_regex (S n) inpcheck EQ_CHECK); auto.
    - intros i inpcheck EQ_CHECK. destruct i as [|[]]; try discriminate.
      specialize (IHact_from_regex (S n) inpcheck EQ_CHECK); auto.
    - (* Quantifier case: more interesting *)
      (* Either we consider the newly introduced check, in which case this is trivial, or we consider another check, in which case we apply IH *)
      intros i inpcheck EQ_CHECK. destruct i as [|[|[|i]]]; try discriminate; simpl in EQ_CHECK.
      + injection EQ_CHECK as <-.
        exists greedy. exists delta. exists r1. reflexivity.
      + specialize (IHact_from_regex (S i) inpcheck EQ_CHECK). auto.
    - (* Apply IH *)
      intros i inpcheck EQ_CHECK. destruct i as [|[|i]]; simpl in EQ_CHECK; try discriminate.
      specialize (IHact_from_regex (S i) inpcheck EQ_CHECK). auto.
    - intros i inpcheck. destruct i as [|[|i]]; discriminate.
  Qed.



  (* Getting the first check from the list of actions *)
  Fixpoint first_check_input (act: actions): option input :=
    match act with
    | [] => None
    | Areg _ :: l | Aclose _ :: l => first_check_input l
    | Acheck inp :: _ => Some inp
    end.

  Inductive is_some_check: option action -> Prop :=
  | Is_some_check: forall inpcheck: input, is_some_check (Some (Acheck inpcheck)).

  Lemma first_check_input_nth_error:
    forall (act: actions) (inpcheck: input),
      first_check_input act = Some inpcheck <->
      exists i, (
        nth_error act i = Some (Acheck inpcheck) /\
        forall j, j < i -> ~is_some_check (nth_error act j)).
  Proof.
    induction act.
    - simpl. split; try discriminate.
      intros [i [ABS _]]. replace (nth_error [] i) with (None (A := action)) in ABS.
      2: { destruct i; simpl; reflexivity. }
      discriminate.
    - destruct (match a with | Acheck _ => true | _ => false end) eqn:IS_CHECK.
      + destruct a as [? | inp | ?]; try discriminate. intro inpcheck. simpl first_check_input. split.
        * intro H. injection H as <-. exists 0. split; auto. intros j LT. inversion LT.
        * intros [i [NTH OTHERS]]. destruct i as [|i]; simpl in NTH.
          -- congruence.
          -- exfalso. specialize (OTHERS 0 ltac:(lia)).
             apply OTHERS. simpl. constructor.
      + replace (first_check_input (a::act)) with (first_check_input act). 2: {
          destruct a; try discriminate; reflexivity.
        }
        intro inpcheck. specialize (IHact inpcheck).
        rewrite IHact. split; intros [i [NTH OTHERS]].
        * exists (S i). split; auto. intros [|j].
          -- intros _. simpl. intro H. destruct a; try discriminate; inversion H.
          -- simpl. intro LT. apply OTHERS. lia.
        * destruct i.
          1: { simpl in NTH. destruct a; discriminate. }
          simpl in NTH.
          exists i. split; auto. intros j LT. apply OTHERS with (j := S j). lia.
  Qed.

  Lemma first_check_input_nth_error2:
    forall act: actions,
      (exists inpcheck, first_check_input act = Some inpcheck) <->
      (exists i inpcheck', nth_error act i = Some (Acheck inpcheck')).
  Proof.
    intro act.
    transitivity (exists inpcheck': input, In (Acheck inpcheck') act).
    - induction act.
      + simpl. firstorder. discriminate.
      + simpl. destruct a.
        * firstorder. discriminate.
        * split.
          -- intros _. exists i. left. reflexivity.
          -- intros _. exists i. reflexivity.
        * firstorder. discriminate.
    - split.
      + intros [inpcheck' IN]. apply In_nth_error in IN.
        destruct IN as [i IN]. exists i. exists inpcheck'. auto.
      + intros [i [inpcheck' NTH]].
        exists inpcheck'. apply nth_error_In with (n := i). auto.
  Qed.

  (* Getting the next regex that follows a check action. *)
  Fixpoint next_check_regex (act: actions): option regex :=
    match act with
    | Acheck _ :: Areg r :: _ => Some r
    | Acheck _ :: _ (* shouldn't happen*) | [] => None
    | Aclose _ :: q | Areg _ :: q => next_check_regex q
    end.

  Lemma next_check_regex_nth_error:
    forall (i: nat) (act: actions) (inpchk: input) (rchk: regex),
      nth_error act i = Some (Acheck inpchk) ->
      (forall j, j < i -> ~is_some_check (nth_error act j)) ->
      nth_error act (S i) = Some (Areg rchk) ->
      next_check_regex act = Some rchk.
  Proof.
    intros i act. revert i. induction act.
    - simpl. discriminate.
    - intros i inpchk rchk EQ_CHECK PREV EQ_RCHK.
      destruct i as [|i]; simpl nth_error in *.
      + injection EQ_CHECK as ->. destruct act; try discriminate.
        injection EQ_RCHK as ->. reflexivity.
      + assert (NOTCHK: match a with | Acheck _ => true | _ => false end = false). {
          specialize (PREV 0 ltac:(lia)). destruct a; try reflexivity.
          exfalso. apply PREV. constructor.
        }
        replace (next_check_regex (a::act)) with (next_check_regex act). 2: {
          symmetry. destruct a; try discriminate; reflexivity.
        }
        apply IHact with (i := i) (inpchk := inpchk); auto.
        intros j LT. apply PREV with (j := S j). lia.
  Qed.

  (* Computes the size of the first chunk of the list of actions passed as argument. *)
  Fixpoint chunk_size (act: actions): nat :=
    match act with
    | Acheck _ :: _ => 0
    | Aclose gid :: l => 1 + chunk_size l
    | Areg r :: l => expanded_size r + chunk_size l
    | [] => 0
    end.

  Fixpoint chunk_length (act: actions): nat :=
    match act with
    | Acheck _ :: _ | [] => 0
    | Aclose _ :: l | Areg _ :: l => 1 + chunk_length l
    end.

  Fixpoint last_chunk_size (act: actions): nat :=
    match first_check_input act, act with
    | Some _, _::q => last_chunk_size q
    | Some _, [] => 0 (* impossible *)
    | None, _ => chunk_size act
    end.



  (** * Extending the bound to lookarounds *)
  Fixpoint regex_lookaround_fuel (str: LWParameters.string) (r: regex): nat :=
    match r with
    | Epsilon | Regex.Character _ => 0
    | Disjunction r1 r2 | Sequence r1 r2 => max (regex_lookaround_fuel str r1) (regex_lookaround_fuel str r2)
    | Quantified _ _ _ r => regex_lookaround_fuel str r
    | Lookaround lk r =>
        let this_lk_fuel := (1 + length str) * expanded_size r in
        this_lk_fuel + regex_lookaround_fuel str r
    | Group _ r => regex_lookaround_fuel str r
    | Anchor _ | Backreference _ => 0
    end.

  Fixpoint actions_lookaround_fuel (str: LWParameters.string) (act: actions): nat :=
    match act with
    | [] => 0
    | Areg r :: act => max (regex_lookaround_fuel str r) (actions_lookaround_fuel str act)
    | Acheck _ :: act | Aclose _ :: act => actions_lookaround_fuel str act
    end.

  (* Computes the actions fuel after taking the first regex into account, but before arriving to the last chunk. *)
  Fixpoint actions_fuel' (act: actions) {struct act}: nat :=
    match act with
    | Acheck _ :: Areg r :: l => (* r must then be a quantifier *)
      match first_check_input l with
      (* Not last chunk *)
      | Some _ => 2 + actions_fuel' l
      (* Last chunk *)
      | None =>
          (* let bonus := if checks_pass then 1 else 0 in
          1 + (bonus + remaining_length inp forward) * last_chunk_size (Areg r :: l) *)
          1
      end
    | Acheck _ :: _ => 0 (* should not happen *)
    | Areg r :: l => expanded_size r + actions_fuel' l
    | Aclose _ :: l => 1 + actions_fuel' l
    | [] => 0 (* should not happen *)
    end.

  (* The actual actions fuel, which starts by treating the first regex specially if there are at least two chunks *)
  Definition actions_fuel_nolk (inp: input) (act: actions) (dir: Direction): nat :=
    match first_check_input act with
    (* Only one (last) chunk: bonus is one *)
    | None => (1 + remaining_length inp dir) * chunk_size act
    (* At least two chunks *)
    | Some inpchk =>
        let b := is_strict_suffix inp inpchk dir in
        let beginning_fuel := match act with
        | Areg (Quantified _ 0 _ r) :: l =>
          (if b then 1 else 3 + expanded_size r) + actions_fuel' l
        | _ => actions_fuel' act
        end in
        let last := ((if b then 1 else 0) + remaining_length inp dir) * last_chunk_size act in
        beginning_fuel + last
    end.

  Definition actions_fuel (inp: input) (act: actions) (dir: Direction): nat :=
    actions_fuel_nolk inp act dir + actions_lookaround_fuel (input_str inp) act.



  (* Invariant: the size of every chunk is less than the size of the next check regex, if any *)
  Lemma chunk_size_lt:
    forall r inp act dir, act_from_regex r inp act dir ->
      forall i acttail, acttail = List.skipn i act ->
        forall rchk, next_check_regex acttail = Some rchk ->
          chunk_size acttail < expanded_size rchk.
  Proof.
    induction 1; try solve[intros i acttail EQ_acttail; apply IHact_from_regex with (i := S i); auto].
    - intros i acttail -> rchk EQ_rchk. destruct i as [|[|i]]; simpl in *; discriminate.
    - intros i acttail EQ_acttail. destruct i as [|i]; simpl in *.
      + specialize (IHact_from_regex 0 _ eq_refl). subst acttail. simpl in *.
        intros rchk EQ_rchk. specialize (IHact_from_regex rchk EQ_rchk). lia.
      + apply IHact_from_regex with (i := S i). auto.
    - intros i acttail EQ_acttail. destruct i as [|i]; simpl in *.
      + specialize (IHact_from_regex 0 _ eq_refl). subst acttail. simpl in *.
        intros rchk EQ_rchk. specialize (IHact_from_regex rchk EQ_rchk). lia.
      + apply IHact_from_regex with (i := S i). auto.
    - intros i acttail EQ_acttail. destruct i as [|[|i]]; simpl in *.
      + specialize (IHact_from_regex 0 _ eq_refl). subst acttail. simpl in *.
        intros rchk EQ_rchk. destruct dir; specialize (IHact_from_regex rchk EQ_rchk); simpl in *; lia.
      + specialize (IHact_from_regex 0 _ eq_refl). subst acttail. simpl in *.
        intros rchk EQ_rchk. destruct dir; specialize (IHact_from_regex rchk EQ_rchk); simpl in *; lia.
      + apply IHact_from_regex with (i := S i). destruct dir; auto.
    - intros i acttail EQ_acttail. destruct i as [|[|i]]; simpl in *;
        subst acttail; simpl; intros rchk H0.
      + specialize (IHact_from_regex 0 _ eq_refl rchk H0). simpl in IHact_from_regex. lia.
      + specialize (IHact_from_regex 0 _ eq_refl rchk H0). simpl in IHact_from_regex. lia.
      + apply IHact_from_regex with (i:= S i); auto.
    - intros i acttail EQ_acttail. destruct i as [|[|i]]; simpl in *.
      + subst acttail. simpl. intros rchk H0. injection H0 as <-. simpl. lia.
      + subst acttail. simpl. intros rchk H0. injection H0 as <-. simpl. lia.
      + specialize (IHact_from_regex i _ eq_refl). subst acttail. simpl in *.
        destruct i as [|i]; simpl in *; intros rchk EQ_rchk; specialize (IHact_from_regex rchk EQ_rchk); lia.
    - intros i acttail EQ_acttail. destruct i as [|[|i]]; simpl in *.
      + subst acttail. specialize (IHact_from_regex 0 _ eq_refl).
        simpl in *. intros rchk EQ_rchk. specialize (IHact_from_regex rchk EQ_rchk). lia.
      + subst acttail. specialize (IHact_from_regex 0 _ eq_refl).
        simpl in *. intros rchk EQ_rchk. specialize (IHact_from_regex rchk EQ_rchk). lia.
      + specialize (IHact_from_regex (S i) _ eq_refl). simpl in *. subst acttail.
        auto.
    - intros i acttail -> rchk. destruct i as [|[|i]]; discriminate.
  Qed.

  Lemma last_chunk_size_skipn:
    forall act i inpchk,
      nth_error act i = Some (Acheck inpchk) ->
      last_chunk_size (skipn (S i) act) = last_chunk_size act.
  Proof.
    induction act.
    - intros i inpchk. replace (nth_error [] i) with (None (A := action)).
      2: { destruct i; reflexivity. }
      discriminate.
    - intros i inpchk NTH.
      destruct i as [|i].
      + simpl in NTH. injection NTH as ->. simpl. reflexivity.
      + change (skipn (S (S i)) (a :: act)) with (skipn (S i) act).
        destruct a.
        * simpl last_chunk_size at 2.
          assert (exists inpchk', first_check_input act = Some inpchk'). {
            apply first_check_input_nth_error2. firstorder.
          }
          destruct H as [inpchk' H]. rewrite H. apply IHact with (inpchk := inpchk). auto.
        * simpl last_chunk_size at 2. apply IHact with (inpchk := inpchk). auto.
        * simpl last_chunk_size at 2.
          assert (exists inpchk', first_check_input act = Some inpchk'). {
            apply first_check_input_nth_error2. firstorder.
          }
          destruct H as [inpchk' H]. rewrite H. apply IHact with (inpchk := inpchk). auto.
  Qed.

  Lemma last_chunk_size_skipn_last:
    forall act i inpcheck,
      nth_error act i = Some (Acheck inpcheck) ->
      first_check_input (skipn (S i) act) = None ->
      last_chunk_size act = chunk_size (skipn (S i) act).
  Proof.
    intros act i inpcheck NTH FSTCHK.
    rewrite <- last_chunk_size_skipn with (i := i) (inpchk := inpcheck) by auto.
    destruct (skipn (S i) act); simpl last_chunk_size; try reflexivity.
    setoid_rewrite FSTCHK. reflexivity.
  Qed.

  Lemma nth_error_nil {A: Type}:
    forall i, nth_error (nil (A := A)) i = None.
  Proof.
    intros i. destruct i; reflexivity.
  Qed.

  Lemma nth_error_skipn {A: Type}:
    forall (l: list A) (a: A) (i: nat),
      nth_error l i = Some a ->
      skipn i l = a :: skipn (S i) l.
  Proof.
    induction l as [|x l IH].
    - intros a i. rewrite nth_error_nil. discriminate.
    - intros a i. destruct i as [|i].
      + simpl. intro H. injection H as <-. reflexivity.
      + simpl. auto.
  Qed.

  Lemma chunk_size_lt_last:
    forall r inp act dir, act_from_regex r inp act dir ->
      forall i acttail, acttail = skipn i act ->
        forall inpchk, first_check_input acttail = Some inpchk ->
        chunk_size acttail < last_chunk_size acttail.
  Proof.
    intros r inp act dir AFR.
    pose proof chunk_size_lt r inp act dir AFR as CHKSZ_LT.
    apply afr_checks_fby_quant in AFR as CHK_FBY_QUANT.
    clear AFR. induction act.
    - intros i acttail EQ_acttail. rewrite skipn_nil in EQ_acttail. subst acttail. discriminate.
    - specialize_prove IHact. {
        intros i acttail EQ_acttail. apply CHKSZ_LT with (i := S i). auto.
      }
      specialize_prove IHact. {
        clear IHact. unfold checks_fby_quant in *.
        intros i inpcheck EQ_inpcheck. apply CHK_FBY_QUANT with (i := S i) (inpcheck := inpcheck). auto.
      }
      intros i acttail EQ_acttail inpchk FSTCHK.
      destruct i as [|i].
      2: {
        apply IHact with (i := i) (inpchk := inpchk); auto.
      }
      simpl in EQ_acttail. subst acttail. simpl in FSTCHK.
      (*destruct (match a with Acheck _ => true | _ => false end) eqn:IS_CHECK.
      (*destruct a as [rsub | inpchk0 | gid].*)
      + destruct a as [rsub | inpchk0 | gid]; try discriminate. simpl.
        unfold checks_fby_quant in CHK_FBY_QUANT.
        specialize (CHK_FBY_QUANT 0 _ eq_refl).
        destruct CHK_FBY_QUANT as [greedy [min [delta [rquant CHK_FBY_QUANT]]]].
        specialize (IHact 0 act eq_refl).
        destruct (first_check_input act) eqn:SNDCHK.
        * specialize (IHact i eq_refl). lia.
        * destruct act as [|a act]; try discriminate. simpl in CHK_FBY_QUANT.
          injection CHK_FBY_QUANT as ->.
          simpl in SNDCHK. simpl. rewrite SNDCHK. lia.
      + *)
      simpl. rewrite FSTCHK.
      (* Idea: apply CHKSZ_LT to show that expanded_size rsub + chunk_size act < expanded_size rchk for some rchk, then apply IHact with acttail = the appropriate tail *)
      specialize (CHKSZ_LT 0 (a :: act) eq_refl).
      unfold checks_fby_quant in CHK_FBY_QUANT.
      pose proof (proj1 (first_check_input_nth_error (a :: act) inpchk)) FSTCHK as [i [FSTCHK_NTH1 FSTCHK_NTH2]].
      specialize (CHK_FBY_QUANT _ _ FSTCHK_NTH1). destruct CHK_FBY_QUANT as [greedy [delta [rquant CHK_FBY_QUANT]]].
      specialize (CHKSZ_LT (Quantified greedy 0 delta rquant)).
      specialize_prove CHKSZ_LT. { eauto using next_check_regex_nth_error. }
      specialize (IHact i _ eq_refl).
      destruct (first_check_input (skipn i act)) as [inpchknext | ] eqn:SNDCHK.
      * specialize (IHact _ eq_refl).
        assert (last_chunk_size (skipn i act) = last_chunk_size act). {
          pose proof last_chunk_size_skipn (a :: act) i inpchk FSTCHK_NTH1.
          simpl in H. rewrite FSTCHK in H. auto.
        }
        assert (expanded_size (Quantified greedy 0 delta rquant) <= chunk_size (skipn i act)). {
          pose proof nth_error_skipn _ _ _ CHK_FBY_QUANT. simpl in H0.
          rewrite H0. simpl. lia.
        }
        simpl in *. lia.
      * assert (last_chunk_size act = chunk_size (skipn i act)). {
          pose proof last_chunk_size_skipn_last (a :: act) i inpchk FSTCHK_NTH1 SNDCHK.
          simpl in H. rewrite FSTCHK in H. auto.
        }
        assert (expanded_size (Quantified greedy 0 delta rquant) <= chunk_size (skipn i act)). {
          pose proof nth_error_skipn _ _ _ CHK_FBY_QUANT. simpl in H0.
          rewrite H0. simpl. lia.
        }
        simpl in *. lia.
  Qed.


  (** * The size of a list of actions coming from a regex is bounded by a polynomial
        in the size of the regex. *)

  Lemma last_chunk_size_nocheck:
    forall l, first_check_input l = None -> last_chunk_size l = chunk_size l.
  Proof.
    intros [] H.
    - simpl. reflexivity.
    - simpl in *. rewrite H. reflexivity.
  Qed.

  Lemma last_chunk_size_lt_regex:
    forall r inp act dir,
      act_from_regex r inp act dir ->
      last_chunk_size act <= expanded_size r.
  Proof.
    induction 1.
    - simpl. lia.
    - simpl in IHact_from_regex. auto.
    - simpl in IHact_from_regex. destruct (first_check_input l) eqn:FSTCHK.
      + auto.
      + rewrite last_chunk_size_nocheck by assumption. lia.
    - simpl in IHact_from_regex. destruct (first_check_input l) eqn:FSTCHK.
      + auto.
      + rewrite last_chunk_size_nocheck by assumption. lia.
    - simpl in IHact_from_regex. destruct (first_check_input l) eqn:FSTCHK.
      + auto.
      + rewrite last_chunk_size_nocheck by assumption. lia.
    - simpl in IHact_from_regex. destruct (first_check_input l) eqn:FSTCHK.
      + simpl. rewrite FSTCHK. auto.
      + simpl. rewrite FSTCHK. lia.
    - simpl in IHact_from_regex. destruct (first_check_input l) eqn:FSTCHK.
      + simpl. rewrite FSTCHK. auto.
      + simpl. rewrite FSTCHK. lia.
    - simpl in IHact_from_regex. destruct (first_check_input l) eqn:FSTCHK.
      + destruct dir; simpl; rewrite FSTCHK; auto.
      + destruct dir; simpl; rewrite FSTCHK; lia.
    - simpl in IHact_from_regex. destruct (first_check_input l) eqn:FSTCHK.
      + auto.
      + rewrite last_chunk_size_nocheck by assumption. lia.
    - simpl in IHact_from_regex. destruct (first_check_input l) eqn:FSTCHK.
      + simpl. rewrite FSTCHK. auto.
      + simpl. rewrite FSTCHK. lia.
    - simpl in *. destruct (first_check_input l); assumption.
    - simpl in IHact_from_regex. destruct (first_check_input l) eqn:FSTCHK.
      + auto.
      + rewrite last_chunk_size_nocheck by assumption. lia.
    - simpl in *. destruct (first_check_input l); lia.
    - simpl. destruct (first_check_input l) as [inpchk|] eqn:FSTCHK.
      + pose proof chunk_size_lt_last _ _ _ _ H 0 (Areg (Lookaround lk rlk) :: l) eq_refl inpchk FSTCHK.
        simpl in H0. rewrite FSTCHK in H0.
        unfold last_chunk_size in IHact_from_regex. simpl in IHact_from_regex.
        rewrite FSTCHK in IHact_from_regex. fold last_chunk_size in IHact_from_regex. lia.
      + unfold last_chunk_size in IHact_from_regex. simpl in IHact_from_regex. rewrite FSTCHK in IHact_from_regex. lia.
    - simpl in *. destruct (first_check_input l) eqn:FSTCHK.
      + auto.
      + rewrite last_chunk_size_nocheck by assumption. lia.
    - simpl in *. destruct (first_check_input l) eqn:FSTCHK.
      + auto.
      + rewrite last_chunk_size_nocheck by assumption. lia.
    - simpl in *. destruct (first_check_input l) eqn:FSTCHK.
      + auto.
      + rewrite last_chunk_size_nocheck by assumption. lia.
  Qed.

  Fixpoint actions_size (act: actions) :=
    match act with
    | [] => 0
    | Acheck _ :: l | Aclose _ :: l => 1 + actions_size l
    | Areg r :: l => expanded_size r + actions_size l
    end.

  Fixpoint sum_to_n (n_min_i: nat) (n: nat) {struct n_min_i} :=
    match n_min_i with
    | 0 => n
    | S n_min_i' => (n - n_min_i) + sum_to_n n_min_i' n
    end.

  Definition num_checks (act: actions) := length (actions_checks act).

  Lemma chunk_size_bound:
    forall r inp act dir, act_from_regex r inp act dir ->
      forall i acttail, acttail = skipn i act ->
        chunk_size acttail <= expanded_size r - num_checks acttail /\ num_checks acttail <= expanded_size r.
  Proof.
    induction 1; try solve[intros i acttail EQ_acttail; apply IHact_from_regex with (i := S i); auto].
    - intros i acttail EQ_acttail. destruct i as [|i]; subst acttail; simpl.
      + unfold num_checks. simpl. lia.
      + rewrite skipn_nil. simpl. unfold num_checks. simpl. lia.
    - (* Disjunction left *)
      intros i acttail EQ_acttail. destruct i as [|i]; subst acttail; simpl.
      + specialize (IHact_from_regex 0 (Areg (Disjunction r1 r2) :: l) eq_refl). simpl in IHact_from_regex.
        unfold num_checks in *. simpl in *. lia.
      + apply IHact_from_regex with (i := S i). auto.
    - (* Disjunction right *)
      intros i acttail EQ_acttail. destruct i as [|i]; subst acttail; simpl.
      + specialize (IHact_from_regex 0 (Areg (Disjunction r1 r2) :: l) eq_refl). simpl in IHact_from_regex.
        unfold num_checks in *. simpl in *. lia.
      + apply IHact_from_regex with (i := S i). auto.
    -
      intros i acttail EQ_acttail. destruct i as [|[|i]]; subst acttail; simpl.
      + specialize (IHact_from_regex 0 (Areg (Sequence r1 r2) :: l) eq_refl). simpl in IHact_from_regex.
        unfold num_checks in *. destruct dir; simpl in *; lia.
      + specialize (IHact_from_regex 0 (Areg (Sequence r1 r2) :: l) eq_refl). simpl in IHact_from_regex.
        unfold num_checks in *. destruct dir; simpl in *; lia.
      + apply IHact_from_regex with (i := S i). destruct dir; auto.
    - (* Forced Quantifier *)
      intros i acttail EQ_acttail. destruct i as [|[|i]]; subst acttail; simpl.
      + specialize (IHact_from_regex 0 _ eq_refl) as [H1 H2].
        unfold num_checks in *. simpl in *. lia.
      + specialize (IHact_from_regex 0 _ eq_refl) as [H1 H2].
        unfold num_checks in *. simpl in *. lia.
      + apply IHact_from_regex with (i := S i); auto.
    - (* Quantifier iteration *)
      intros i acttail EQ_acttail. destruct i as [|[|[|i]]]; simpl in *.
      + subst acttail. specialize (IHact_from_regex 0 (Areg (Quantified greedy 0 (NoI.N 1 + delta)%NoI r1) :: l) eq_refl).
        simpl in IHact_from_regex. simpl. unfold num_checks in *. simpl in *. lia.
      + subst acttail. specialize (IHact_from_regex 0 (Areg (Quantified greedy 0 (NoI.N 1 + delta)%NoI r1) :: l) eq_refl).
        simpl in IHact_from_regex. simpl. unfold num_checks in *. simpl in *. lia.
      + subst acttail. specialize (IHact_from_regex 0 (Areg (Quantified greedy 0 (NoI.N 1 + delta)%NoI r1) :: l) eq_refl).
        simpl in IHact_from_regex. simpl. unfold num_checks in *. simpl in *. lia.
      + apply IHact_from_regex with (i := S i). auto.
    -
      intros i acttail EQ_acttail. destruct i as [|[|i]]; subst acttail; simpl.
      + specialize (IHact_from_regex 0 (Areg (Group gid r1) :: l) eq_refl).
        unfold num_checks in *. simpl in *. lia.
      + specialize (IHact_from_regex 0 (Areg (Group gid r1) :: l) eq_refl).
        unfold num_checks in *. simpl in *. lia.
      + apply IHact_from_regex with (i := S i). auto.
    - intros i acttail EQ_acttail. destruct i as [|[|i]]; subst acttail; unfold num_checks; simpl in *; try lia.
      split; try lia.
      specialize (IHact_from_regex 0 (Areg (Lookaround lk rlk) :: l) eq_refl). simpl in IHact_from_regex. lia.
  Qed.

  Lemma actions_size_decomp_check:
    forall act inpcheck,
      first_check_input act = Some inpcheck ->
      actions_size act = chunk_size act + 1 + actions_size (skipn (S (chunk_length act)) act).
  Proof.
    induction act as [|a act IH]; [|destruct a].
    - simpl. discriminate.
    - intros inpcheck EQ_inpcheck. simpl in *. rewrite IH with (inpcheck := inpcheck). lia. auto.
    - simpl. reflexivity.
    - intros inpcheck EQ_inpcheck. simpl in *. rewrite IH with (inpcheck := inpcheck). lia. auto.
  Qed.

  Lemma actions_size_decomp_nocheck:
    forall act,
      first_check_input act = None ->
      actions_size act = chunk_size act.
  Proof.
    induction act.
    - reflexivity.
    - destruct a.
      + simpl. intro H. specialize (IHact H). congruence.
      + discriminate.
      + simpl. intro H. specialize (IHact H). congruence.
  Qed.

  Lemma num_checks_skipn_chunk_length:
    forall act inpcheck,
      first_check_input act = Some inpcheck ->
      num_checks act = 1 + num_checks (skipn (S (chunk_length act)) act).
  Proof.
    induction act.
    - discriminate.
    - destruct (match a with Acheck _ => true | _ => false end) eqn:IS_CHECK.
      + destruct a; try discriminate. simpl. reflexivity.
      + intros inpcheck FSTCHK.
        replace (num_checks (a :: act)) with (num_checks act).
        2: { destruct a; try discriminate; reflexivity. }
        replace (chunk_length (a :: act)) with (S (chunk_length act)).
        2: { destruct a; try discriminate; reflexivity. }
        apply IHact with (inpcheck := inpcheck).
        transitivity (first_check_input (a :: act)); auto.
        destruct a; try discriminate; reflexivity.
  Qed.

  Lemma num_checks_no_check:
    forall act, first_check_input act = None -> num_checks act = 0.
  Proof.
    induction act.
    - reflexivity.
    - intro H. destruct a; try discriminate; unfold num_checks in *; simpl in *; auto.
  Qed.

  Theorem actions_size_bound:
    forall r inp act dir, act_from_regex r inp act dir ->
      forall i acttail, acttail = skipn i act ->
        actions_size acttail <= num_checks acttail + sum_to_n (num_checks acttail) (expanded_size r).
  Proof.
    intros r inp act dir AFR. pose proof chunk_size_bound r inp act dir AFR as CHK_BOUND.
    clear AFR inp. induction act.
    - intros i acttail. rewrite skipn_nil. intros ->. simpl. lia.
    - specialize_prove IHact. {
        intros i acttail EQ_acttail. apply CHK_BOUND with (i := S i). auto.
      }
      intros i acttail EQ_acttail. destruct i as [|i].
      + simpl in EQ_acttail. subst acttail.
        destruct a.
        * unfold num_checks in *. destruct (first_check_input act) eqn:FSTCHK.
          -- rewrite actions_size_decomp_check with (inpcheck := i) by auto.
             setoid_rewrite num_checks_skipn_chunk_length with (act := Areg r0 :: act) (inpcheck := i); auto. unfold num_checks.
             specialize (IHact (chunk_length (Areg r0 :: act)) _ eq_refl).
             change (skipn (S (chunk_length (Areg r0 :: act))) (Areg r0 :: act)) with (skipn (chunk_length (Areg r0 :: act)) act).
             specialize (CHK_BOUND 0 (Areg r0 :: act) eq_refl).
             set (n := length (actions_checks _)). simpl sum_to_n. subst n.
             setoid_rewrite <- num_checks_skipn_chunk_length with (act := Areg r0 :: act) (inpcheck := i) at 2; auto.
             unfold num_checks. lia.
          -- rewrite actions_size_decomp_nocheck; auto.
             specialize (CHK_BOUND 0 (Areg r0 :: act) eq_refl).
             setoid_rewrite num_checks_no_check; auto.
             setoid_rewrite num_checks_no_check in CHK_BOUND; auto.
             simpl in *. lia.

        * unfold num_checks in *. simpl.
          specialize (IHact 0 act eq_refl). lia.
        * unfold num_checks in *. destruct (first_check_input act) eqn:FSTCHK.
          -- rewrite actions_size_decomp_check with (inpcheck := i) by auto.
             setoid_rewrite num_checks_skipn_chunk_length with (act := Aclose g :: act) (inpcheck := i); auto. unfold num_checks.
             specialize (IHact (chunk_length (Aclose g :: act)) _ eq_refl).
             change (skipn (S (chunk_length (Aclose g :: act))) (Aclose g :: act)) with (skipn (chunk_length (Aclose g :: act)) act).
             specialize (CHK_BOUND 0 (Aclose g :: act) eq_refl).
             set (n := length (actions_checks _)). simpl sum_to_n. subst n.
             setoid_rewrite <- num_checks_skipn_chunk_length with (act := Aclose g :: act) (inpcheck := i) at 2; auto.
             unfold num_checks. lia.
          -- rewrite actions_size_decomp_nocheck; auto.
             specialize (CHK_BOUND 0 (Aclose g :: act) eq_refl).
             setoid_rewrite num_checks_no_check; auto.
             setoid_rewrite num_checks_no_check in CHK_BOUND; auto.
             simpl in *. lia.
      + simpl in EQ_acttail. apply IHact with (i := i). auto.
  Qed.

  Lemma sum_to_n_bound':
    forall n_min_i k n, sum_to_n n_min_i n <= sum_to_n (k + n_min_i) n.
  Proof.
    intros n_min_i k n. induction k.
    - reflexivity.
    - simpl. lia.
  Qed.

  Lemma sum_to_n_overshoot:
    forall k n, sum_to_n (k + n) n = sum_to_n n n.
  Proof.
    intros k n. induction k.
    - reflexivity.
    - simpl. replace (n - S (k + n)) with 0 by lia. auto.
  Qed.

  Lemma sum_to_n_bound:
    forall n_min_i n, sum_to_n n_min_i n <= sum_to_n n n.
  Proof.
    intros n_min_i n. destruct (PeanoNat.Nat.le_decidable n_min_i n).
    - set (k := n - n_min_i). replace n with (k + n_min_i) at 2 by lia. apply sum_to_n_bound'.
    - set (k := n_min_i - n). replace n_min_i with (k + n) by lia. rewrite sum_to_n_overshoot. reflexivity.
  Qed.

  Lemma sum_to_n_sum_seq:
    forall n_min_i n, n_min_i <= n ->
      sum_to_n n_min_i n = list_sum (seq (n - n_min_i) (S n_min_i)).
  Proof.
    intros n_min_i n LE. induction n_min_i.
    - rewrite PeanoNat.Nat.sub_0_r. simpl. lia.
    - simpl. f_equal.
      specialize (IHn_min_i ltac:(lia)). rewrite IHn_min_i.
      simpl. replace (S (S (n - S n_min_i))) with (S (n - n_min_i)) by lia. lia.
  Qed.

  Lemma sum_to_n_n_sum_seq:
    forall n, sum_to_n n n = list_sum (seq 0 (S n)).
  Proof.
    intro n. rewrite sum_to_n_sum_seq by reflexivity.
    f_equal. f_equal. apply PeanoNat.Nat.sub_diag.
  Qed.

  (* Classical formula... *)
  Lemma sum_to_n_n_formula:
    forall n, sum_to_n n n = PeanoNat.Nat.div2 (n * S n).
  Proof.
    intro n. rewrite sum_to_n_n_sum_seq. induction n.
    - simpl. reflexivity.
    - replace (S (S n)) with (S n + 1) at 1 by lia. rewrite seq_app.
      rewrite list_sum_app, IHn. simpl list_sum.
      rewrite PeanoNat.Nat.add_0_r.
      destruct (PeanoNat.Nat.Even_Odd_dec n).
      + destruct e as [m e]. subst n.
        replace (2 * m * S (2 * m)) with (2 * (m * S (2 * m))) by lia.
        replace (S (S (2 * m))) with (2 * S m) by lia.
        replace (S (2 * m) * (2 * S m)) with (2 * (S (2 * m) * S m)) by lia.
        do 2 rewrite PeanoNat.Nat.div2_double. lia.
      + destruct o as [m o]. subst n.
        replace (S (2 * m + 1)) with (2 * S m) by lia.
        replace ((2*m+1)*(2*S m)) with (2*((2*m+1)*S m)) by lia.
        replace (2*S m*S (2*S m)) with (2*(S m*S (2*S m))) by lia.
        do 2 rewrite PeanoNat.Nat.div2_double. lia.
  Qed.

  (* The main corollary for bounding the size of the list of actions *)
  Corollary actions_size_bound' {r inp act dir}:
      act_from_regex r inp act dir ->
      actions_size act
      <= expanded_size r + PeanoNat.Nat.div2 (expanded_size r * S (expanded_size r)).
  Proof.
    intro AFR.
    pose proof actions_size_bound r inp act dir AFR 0 act eq_refl.
    pose proof chunk_size_bound r inp act dir AFR 0 act eq_refl as [_ CHK].
    pose proof sum_to_n_bound (num_checks act) (expanded_size r).
    pose proof sum_to_n_n_formula (expanded_size r).
    lia.
  Qed.

  Lemma is_strict_suffix_incr:
    forall inp nextinp inpchk dir,
      advance_input inp dir = Some nextinp ->
      Bool.le (is_strict_suffix inp inpchk dir) (is_strict_suffix nextinp inpchk dir).
  Proof.
    intros inp nextinp inpchk dir ADV.
    apply Bool.le_implb, Bool.implb_true_iff.
    intro SS. apply is_strict_suffix_correct. apply is_strict_suffix_correct in SS.
    eapply ss_next; eauto.
  Qed.

  Lemma is_strict_suffix_incr':
    forall inp n nextinp inpchk dir,
      advance_input_n inp n dir = nextinp ->
      Bool.le (is_strict_suffix inp inpchk dir) (is_strict_suffix nextinp inpchk dir).
  Proof.
    intros inp n nextinp inpchk dir ADV.
    apply Bool.le_implb, Bool.implb_true_iff.
    intro SS. apply is_strict_suffix_correct. apply is_strict_suffix_correct in SS.
    symmetry in ADV.
    destruct (advance_input_n_suffix _ _ _ nextinp ADV).
    - rewrite H. auto.
    - eapply strict_suffix_trans; eauto.
  Qed.

  (* TODO Move to Linden *)
  Lemma remaining_length_current_str:
    forall inp dir, remaining_length inp dir = length (current_str inp dir).
  Proof.
    intros [next pref] []; reflexivity.
  Qed.

  Lemma remaining_length_advance_input_n_diff:
    forall inp n nextinp dir,
      advance_input_n inp n dir = nextinp -> nextinp <> inp ->
      remaining_length nextinp dir < remaining_length inp dir.
  Proof.
    intros inp n nextinp dir ADV NEQ.
    unfold advance_input_n in ADV. destruct inp as [next pref].
    destruct dir; subst nextinp; simpl; destruct n as [|n]; try contradiction.
    - destruct next as [|x next]; try contradiction.
      simpl. rewrite length_skipn. lia.
    - destruct pref as [|x pref]; try contradiction.
      simpl. rewrite length_skipn. lia.
  Qed.

  Lemma read_decreases_fuel_nolk:
    forall inp cd nextinp cont dir,
      advance_input inp dir = Some nextinp ->
      actions_fuel_nolk inp (Areg (Regex.Character cd) :: cont) dir > actions_fuel_nolk nextinp cont dir.
  Proof.
    intros inp cd nextinp cont dir EQ_nextinp.
    unfold actions_fuel_nolk. simpl first_check_input.
    destruct first_check_input as [inpchk|] eqn:FSTCHK.
    - simpl actions_fuel'.
      replace (last_chunk_size (Areg _ :: cont)) with (last_chunk_size cont).
      2: { unfold last_chunk_size at 2. simpl first_check_input.
        rewrite FSTCHK. reflexivity. }
      assert (((if is_strict_suffix inp inpchk dir then 1 else 0) +
remaining_length inp dir) * last_chunk_size cont >= ((if is_strict_suffix nextinp inpchk dir then 1 else 0) +
remaining_length nextinp dir) * last_chunk_size cont). {
        unfold ge.
        apply PeanoNat.Nat.mul_le_mono_r.
        replace (remaining_length inp dir) with (S (remaining_length nextinp dir)).
        2: {
          symmetry. do 2 rewrite remaining_length_current_str. apply advance_current_plus_one. auto.
        }
        pose proof is_strict_suffix_incr inp nextinp inpchk dir EQ_nextinp.
        destruct is_strict_suffix; destruct is_strict_suffix; try discriminate; lia.
      }
      destruct cont as [|[r | ? | ?] l]; simpl in *; try lia.
      destruct r; try lia.
      destruct min; try lia.
      assert ((if (is_strict_suffix nextinp inpchk dir: bool) then 1 else S (S (S (expanded_size r)))) <= expanded_size (Quantified greedy 0 delta r)). {
        simpl. destruct (is_strict_suffix nextinp inpchk dir); lia.
      }
      lia.
    - simpl. unfold gt. apply le_lt_S.
      apply PeanoNat.Nat.add_le_mono_l.
      replace (remaining_length inp dir) with (S (remaining_length nextinp dir)).
      2: {
        symmetry. do 2 rewrite remaining_length_current_str. apply advance_current_plus_one. auto.
      }
      simpl. lia.
  Qed.

  (* TODO Move to Linden *)
  Lemma advance_input_samestr:
    forall inp nextinp dir,
      advance_input inp dir = Some nextinp ->
      input_str nextinp = input_str inp.
  Proof.
    intros inp nextinp dir ADV. unfold advance_input in ADV.
    destruct inp as [next pref]. destruct dir.
    - destruct next as [|x next]; try discriminate.
      injection ADV as <-. simpl. rewrite <- app_assoc. reflexivity.
    - destruct pref as [|x pref]; try discriminate.
      injection ADV as <-. simpl. rewrite <- app_assoc. reflexivity.
  Qed.

  Lemma read_decreases_fuel:
    forall inp cd nextinp cont dir,
      advance_input inp dir = Some nextinp ->
      actions_fuel inp (Areg (Regex.Character cd) :: cont) dir > actions_fuel nextinp cont dir.
  Proof.
    intros inp cd nextinp cont dir ADV. unfold actions_fuel.
    simpl actions_lookaround_fuel.
    rewrite advance_input_samestr with (nextinp := nextinp) (inp := inp) (dir := dir) by auto.
    pose proof read_decreases_fuel_nolk inp cd nextinp cont dir ADV. lia.
  Qed.

  (* TODO Move to Linden *)
  Lemma advance_input_n_samestr:
    forall inp nextinp n dir,
      advance_input_n inp n dir = nextinp ->
      input_str nextinp = input_str inp.
  Proof.
    intros inp nextinp n dir ADV. unfold advance_input_n in ADV.
    destruct inp as [next pref]. destruct dir; subst nextinp; simpl.
    - rewrite rev_app_distr, rev_involutive, <- app_assoc, firstn_skipn. reflexivity.
    - rewrite app_assoc, <- rev_app_distr, firstn_skipn. reflexivity.
  Qed.

  Lemma read_backref_decreases_fuel_nolk:
    forall inp gid n nextinp cont dir,
      advance_input_n inp n dir = nextinp ->
      actions_fuel_nolk inp (Areg (Backreference gid) :: cont) dir > actions_fuel_nolk nextinp cont dir.
  Proof.
    intros inp gid n nextinp cont dir EQ_nextinp.
    unfold actions_fuel_nolk. simpl first_check_input.
    destruct first_check_input as [inpchk|] eqn:FSTCHK.
    - simpl actions_fuel'.
      replace (last_chunk_size (Areg _ :: cont)) with (last_chunk_size cont).
      2: { simpl.  rewrite FSTCHK. reflexivity. }
      assert (((if is_strict_suffix inp inpchk dir then 1 else 0) +
      remaining_length inp dir) * last_chunk_size cont >= ((if is_strict_suffix nextinp inpchk dir then 1 else 0) +
      remaining_length nextinp dir) * last_chunk_size cont). {
        apply PeanoNat.Nat.mul_le_mono_r.
        destruct (Chars.input_eq_dec inp nextinp).
        { rewrite <- e. reflexivity. }
        pose proof is_strict_suffix_incr' inp n nextinp inpchk dir EQ_nextinp.
        pose proof remaining_length_advance_input_n_diff inp n nextinp dir EQ_nextinp.
        specialize_prove H0. { symmetry. auto. }
        destruct is_strict_suffix; destruct is_strict_suffix; try discriminate; lia.
      }
      destruct cont as [|[r | ? | ?] l]; simpl in *; try lia.
      destruct r; try lia.
      destruct min; try lia.
      assert ((if (is_strict_suffix nextinp inpchk dir: bool) then 1 else S (S (S (expanded_size r)))) <= expanded_size (Quantified greedy 0 delta r)). {
        simpl. destruct (is_strict_suffix nextinp inpchk dir); lia.
      }
      lia.
    - simpl. unfold gt. apply le_lt_S.
      apply PeanoNat.Nat.add_le_mono_l.
      assert (remaining_length nextinp dir <= remaining_length inp dir). {
        destruct (input_eq_dec nextinp inp).
        - rewrite e. auto.
        - pose proof remaining_length_advance_input_n_diff inp n nextinp dir EQ_nextinp n0. lia.
      } (* Follows from EQ_nextinp *)
      apply PeanoNat.Nat.mul_le_mono_nonneg; lia.
  Qed.

  Lemma read_backref_decreases_fuel:
    forall inp gid n nextinp cont dir,
      advance_input_n inp n dir = nextinp ->
      actions_fuel inp (Areg (Backreference gid) :: cont) dir > actions_fuel nextinp cont dir.
  Proof.
    intros inp gid n nextinp cont dir ADV.
    unfold actions_fuel.
    rewrite advance_input_n_samestr with (nextinp := nextinp) (inp := inp) (dir := dir) (n := n) by auto.
    pose proof read_backref_decreases_fuel_nolk inp gid n nextinp cont dir ADV.
    simpl actions_lookaround_fuel. lia.
  Qed.

  Lemma actions_fuel_nolk_notlast_le:
    forall inp act inpchk dir,
      first_check_input act = Some inpchk ->
      actions_fuel_nolk inp act dir <=
        actions_fuel' act +
        ((if is_strict_suffix inp inpchk dir then 1 else 0) + remaining_length inp dir) * last_chunk_size act.
  Proof.
    intros inp act inpchk dir FSTCHK. unfold actions_fuel_nolk.
    rewrite FSTCHK.
    destruct act as [|[r | ? | ?] l]; try reflexivity.
    destruct r; try reflexivity.
    destruct min; try reflexivity.
    destruct is_strict_suffix; simpl; lia.
  Qed.

  Lemma strict_suffix_irrefl:
    forall dir inp, ~strict_suffix inp inp dir.
  Proof.
    intros dir inp SS.
    apply ss_neq in SS. contradiction.
  Qed.

  Lemma actions_checks_first_check_input:
    forall cont inpchk, first_check_input cont = Some inpchk ->
      exists tl, actions_checks cont = inpchk :: tl.
  Proof.
    intros cont inpchk. induction cont.
    - discriminate.
    - destruct a as [r | i | g]; simpl; auto.
      intro H. injection H as ->. eexists. reflexivity.
  Qed.

  Lemma read_backref_advance_input_n:
    forall rer gm gid inp br_str nextinp dir,
      read_backref rer gm gid inp dir = Some (br_str, nextinp) ->
      exists n, nextinp = advance_input_n inp n dir.
  Proof.
    intros rer gm gid inp br_str nextinp dir H.
    unfold read_backref in H.
    destruct (Groups.GroupMap.find gid gm) as [range |].
    2: { injection H as <- <-. exists 0. destruct inp; destruct dir; reflexivity. }
    destruct range as [startIdx [endIdx |]].
    2: { injection H as <- <-. exists 0. destruct inp; destruct dir; reflexivity. }
    destruct inp as [next pref].
    destruct dir.
    - destruct Nat.leb; try discriminate.
      destruct EqDec.eqb; try discriminate.
      injection H as <- <-. exists (endIdx - startIdx). reflexivity.
    - destruct Nat.leb; try discriminate.
      destruct EqDec.eqb; try discriminate.
      injection H as <- <-. exists (endIdx - startIdx). reflexivity.
  Qed.

  Lemma remaining_le_full_length:
    forall inp dir, remaining_length inp dir <= length (input_str inp).
  Proof.
    intros [next pref] []; simpl.
    - rewrite length_app. lia.
    - rewrite length_app, length_rev. lia.
  Qed.

  Lemma succ_noi_pred:
    forall ninf, match ninf with NoI.N 0 => true | _ => false end = false ->
      (NoI.N 1 + noi_pred ninf)%NoI = ninf.
  Proof.
    intros ninf NON_ZERO.
    destruct ninf as [[|]|]; try discriminate; simpl; try reflexivity.
    rewrite PeanoNat.Nat.sub_0_r. reflexivity.
  Qed.

  Lemma max_max_same:
    forall a b: nat, Nat.max a (Nat.max a b) = Nat.max a b.
  Proof. lia. Qed.

  (* termination proof about compte_result *)

  Theorem result_terminates':
    forall (r: regex) (inp: input) (act: actions) (dir: Direction),
      act_from_regex r inp act dir ->
      forall fuel, fuel > actions_fuel inp act dir ->
        forall gm rer, compute_result rer act inp gm dir fuel <> Out_of_fuel.
  Proof.
    intros r inp act dir AFR fuel.
    revert inp act dir AFR. induction fuel.
    - lia.
    - intros inp act dir AFR FUEL gm rer. simpl.
      destruct act as [ | [[] | inpcheck | gid] cont ].
      + discriminate.
      + apply IHfuel with (dir := dir).
        { apply afr_pop_epsilon. auto. }
        unfold actions_fuel, actions_fuel_nolk in FUEL. unfold actions_fuel, actions_fuel_nolk.
        simpl in FUEL.
        destruct first_check_input as [inpchk|] eqn:FSTCHK.
        * destruct cont as [|[] cont]; try lia.
          destruct r0; try lia.
          destruct min; try lia.
          simpl in FUEL, FSTCHK. simpl.
          rewrite FSTCHK in FUEL. rewrite FSTCHK.
          destruct is_strict_suffix; lia.
        * lia.
      + (* Read *) destruct read_char as [[c nextinp]|] eqn:READ; try discriminate.
        specialize (IHfuel nextinp cont dir).
        specialize_prove IHfuel. { apply afr_pop_char with (inp := inp) (cd := cd).
        1: auto. eapply read_char_success_advance; eauto. }
        specialize_prove IHfuel. {
          pose proof read_decreases_fuel inp cd nextinp cont dir.
          specialize_prove H. { eapply read_char_success_advance; eauto. }
          lia.
        }
        specialize (IHfuel gm rer).
        destruct compute_result; try discriminate; auto.
      +
        unfold actions_fuel, actions_fuel_nolk in FUEL.
        destruct first_check_input as [inpchk|] eqn:FSTCHK.
        * simpl in FSTCHK, FUEL.
          assert (IH1: compute_result rer (Areg r1 :: cont) inp gm dir fuel <> Out_of_fuel). {
            apply IHfuel.
            - eapply afr_pop_disj_l; eauto.
            - pose proof actions_fuel_nolk_notlast_le inp (Areg r1 :: cont) inpchk dir.
              specialize (H FSTCHK).
              simpl in H. rewrite FSTCHK in FUEL, H. unfold actions_fuel. simpl. lia.
          }
          assert (IH2: compute_result rer (Areg r2 :: cont) inp gm dir fuel <> Out_of_fuel). {
            apply IHfuel.
            - eapply afr_pop_disj_r; eauto.
            - pose proof actions_fuel_nolk_notlast_le inp (Areg r2 :: cont) inpchk dir.
              specialize (H FSTCHK).
              simpl in H. rewrite FSTCHK in FUEL, H. unfold actions_fuel. simpl. lia.
          }
          destruct (compute_result rer (Areg r1 :: cont) inp gm dir fuel); try contradiction; auto.
        * simpl in FSTCHK.
          assert (IH1: compute_result rer (Areg r1 :: cont) inp gm dir fuel <> Out_of_fuel). {
            apply IHfuel.
            - eapply afr_pop_disj_l; eauto.
            - unfold actions_fuel, actions_fuel_nolk. simpl first_check_input. rewrite FSTCHK.
              simpl chunk_size in *.
              unfold gt in FUEL. unfold gt.
              assert ((1 + remaining_length inp dir) * (expanded_size r1 + chunk_size cont) < (1 + remaining_length inp dir) * S (expanded_size r1 + expanded_size r2 + chunk_size cont)). {
                apply PeanoNat.Nat.mul_lt_mono_pos_l; lia.
              }
              simpl actions_lookaround_fuel in *. lia.
          }
          assert (IH2: compute_result rer (Areg r2 :: cont) inp gm dir fuel <> Out_of_fuel). {
            apply IHfuel.
            - eapply afr_pop_disj_r; eauto.
            - unfold actions_fuel, actions_fuel_nolk. simpl first_check_input. rewrite FSTCHK.
              simpl chunk_size in *.
              unfold gt in FUEL. unfold gt.
              assert ((1 + remaining_length inp dir) * (expanded_size r1 + chunk_size cont) < (1 + remaining_length inp dir) * S (expanded_size r1 + expanded_size r2 + chunk_size cont)). {
                apply PeanoNat.Nat.mul_lt_mono_pos_l; lia.
              }
              simpl actions_lookaround_fuel in *. lia.
          }
          destruct (compute_result rer (Areg r1 :: cont) inp gm dir fuel); try contradiction; auto.
      + (* Sequence *)
        unfold actions_fuel, actions_fuel_nolk in FUEL. destruct first_check_input as [inpchk|] eqn:FSTCHK.
        * simpl in FUEL.
          apply IHfuel.
          1: apply afr_pop_sequence; auto.
          pose proof actions_fuel_nolk_notlast_le inp (seq_list r1 r2 dir ++ cont) inpchk dir.
          specialize_prove H. {
            destruct dir; apply FSTCHK.
          }
          unfold actions_fuel.
          destruct dir; simpl in H; simpl first_check_input in FSTCHK; rewrite FSTCHK in FUEL, H;
          simpl; lia.
        * simpl actions_lookaround_fuel in FUEL.
          apply IHfuel. 1: apply afr_pop_sequence; auto.
          unfold actions_fuel, actions_fuel_nolk.
          replace (first_check_input (seq_list r1 r2 dir ++ cont)) with (None (A := input)). 2: {
            symmetry. destruct dir; setoid_rewrite FSTCHK; reflexivity.
          }
          simpl chunk_size in *.
          replace (chunk_size (seq_list r1 r2 dir ++ cont)) with (expanded_size r1 + expanded_size r2 + chunk_size cont). 2: {
            destruct dir; simpl; lia.
          }
          unfold gt in FUEL. unfold gt.
          assert ((1 + remaining_length inp dir) * (expanded_size r1 + expanded_size r2 + chunk_size cont) < (1 + remaining_length inp dir) * S (expanded_size r1 + expanded_size r2 + chunk_size cont)). {
            apply PeanoNat.Nat.mul_lt_mono_pos_l; lia.
          }
          destruct dir; simpl; lia.
      + (* Quantified *)
        destruct min.
        (* forced quantifier *)
        2:{
          specialize (IHfuel inp (Areg r1::Areg(Quantified greedy min delta r1)::cont) dir).
          specialize_prove IHfuel.
          { apply afr_pop_quant_forced. auto. }
          specialize_prove IHfuel.
          {
            unfold actions_fuel, actions_fuel_nolk in FUEL. unfold actions_fuel, actions_fuel_nolk.
            simpl first_check_input in *. simpl actions_lookaround_fuel in *.
            rewrite max_max_same.
            destruct first_check_input as [inpchk|] eqn:FSTCHK.
            2: {
              simpl chunk_size in *. lia.
            }
            simpl last_chunk_size in *. rewrite FSTCHK in *.
            destruct r1; try (simpl in *; lia).
            destruct min0; try (simpl in *; lia).
            destruct is_strict_suffix; try (simpl in *; lia).
          }
          destruct (compute_result) eqn:COMP; try discriminate.
          apply IHfuel in COMP. inversion COMP. }
        destruct (match delta with NoI.N 0 => true | _ => false end) eqn:ZERO.
        * destruct delta as [[]|]; try discriminate.
          apply IHfuel.
          1: eapply afr_pop_quant_done; eauto.
          unfold actions_fuel, actions_fuel_nolk in FUEL. unfold actions_fuel.
          simpl actions_lookaround_fuel in FUEL.
          simpl in FUEL.
          destruct (first_check_input cont) as [inpchk|] eqn:FSTCHK.
          -- pose proof actions_fuel_nolk_notlast_le inp cont inpchk dir FSTCHK.
             destruct (is_strict_suffix inp inpchk dir); lia.
          -- unfold actions_fuel_nolk. rewrite FSTCHK. lia.
        (* subst greedy0 min delta r0. *)
        * (* simplifying the expression without duplication *)
          set (x := match compute_result rer _ inp _ dir fuel with | Out_of_fuel => Out_of_fuel | NoMatch => _ | Success lf => _  end).
          set (y := match compute_result rer _ inp _ dir fuel with | Out_of_fuel => Out_of_fuel | NoMatch => _ | Success lf => _  end).
          replace (match delta with | NoI.N 0 => _ | _ => if greedy then x else y end) with (if greedy then x else y).
          2: {
            destruct delta as [[]|]; try discriminate; reflexivity.
          }
          subst x. subst y.
          assert (IHiter: compute_result rer (Areg r1 :: Acheck inp :: Areg (Quantified greedy 0 (noi_pred delta) r1) :: cont) inp (Groups.GroupMap.reset (def_groups r1) gm) dir fuel <> Out_of_fuel). {
            apply IHfuel.
            - apply afr_pop_quant_free_iter.
              rewrite succ_noi_pred by auto. auto.
            - unfold actions_fuel, actions_fuel_nolk. simpl first_check_input. cbv match.
              replace (is_strict_suffix inp inp dir) with false.
              2: {
                symmetry. apply is_strict_suffix_inv_false.
                apply strict_suffix_irrefl.
              }
              destruct (match r1 with Quantified _ _ _ _ => true | _ => false end) eqn:R1_QUANT.
              + destruct r1; try discriminate. simpl actions_fuel'.
                unfold actions_fuel, actions_fuel_nolk in FUEL. simpl first_check_input in FUEL.
                destruct first_check_input as [inpchk | ] eqn:FSTCHK.
                * simpl last_chunk_size in *. rewrite FSTCHK in FUEL. rewrite FSTCHK.
                  destruct (is_strict_suffix inp inpchk dir) eqn:SS.
                  -- simpl in *.
                    assert (expanded_size (Quantified greedy 0 delta (Quantified greedy0 min delta0 r1)) <= last_chunk_size cont). {
                      pose proof chunk_size_lt_last r inp _ dir AFR 0 _ eq_refl inpchk FSTCHK. simpl in H.
                      rewrite FSTCHK in H. simpl. lia.
                    }
                    simpl in H.
                    destruct min; lia.
                  -- simpl in *. destruct min; lia.
                * simpl in FUEL. simpl. rewrite FSTCHK. destruct min; lia.
              + replace (match r1 with | Quantified _ _ _ r0 => _ | _ => _ end) with (actions_fuel' (Areg r1 :: Acheck inp :: Areg (Quantified greedy 0 (noi_pred delta) r1) :: cont)).
                2: { destruct r1; try discriminate; reflexivity. }
                unfold actions_fuel, actions_fuel_nolk in FUEL. simpl first_check_input in FUEL.
                simpl. destruct first_check_input as [inpchk | ] eqn:FSTCHK.
                * simpl last_chunk_size in *. rewrite FSTCHK in FUEL.
                  destruct (is_strict_suffix inp inpchk dir) eqn:SS.
                  -- simpl in *.
                    assert (expanded_size (Quantified greedy 0 delta r1) <= last_chunk_size cont). {
                      pose proof chunk_size_lt_last r inp _ dir AFR 0 _ eq_refl inpchk FSTCHK. simpl in H.
                      rewrite FSTCHK in H. simpl. lia.
                    }
                    simpl in H.
                    lia.
                  -- simpl in *. lia.
                * simpl in *. lia.
          }
          assert (IHskip: compute_result rer cont inp gm dir fuel <> Out_of_fuel). {
            apply IHfuel.
            - eapply afr_pop_quant_free_skip with (greedy := greedy) (delta := noi_pred delta). rewrite succ_noi_pred by auto. apply AFR.
            - unfold actions_fuel, actions_fuel_nolk in FUEL.
              simpl first_check_input in FUEL.
              destruct first_check_input as [inpchk | ] eqn:FSTCHK.
              + pose proof actions_fuel_nolk_notlast_le inp cont inpchk dir FSTCHK.
                assert ((if is_strict_suffix inp inpchk dir then 1 else 3 + expanded_size r1) >= 1). { destruct (is_strict_suffix inp inpchk dir); lia. }
                simpl last_chunk_size in FUEL. rewrite FSTCHK in FUEL.
                unfold actions_fuel. simpl actions_lookaround_fuel in FUEL.
                lia.
              + simpl in FUEL. unfold actions_fuel, actions_fuel_nolk. rewrite FSTCHK. simpl. lia.
          }
          destruct greedy; destruct compute_result; auto;
            destruct compute_result; auto.
      + (* Lookaround *)
        assert (LKCONT: compute_result rer [Areg r0] inp gm (lk_dir lk) fuel <> Out_of_fuel). {
          apply IHfuel.
          1: eapply afr_pop_lk_lk; eauto.
          unfold actions_fuel in *. simpl actions_lookaround_fuel in *.
          unfold actions_fuel_nolk. simpl.
          rewrite PeanoNat.Nat.max_0_r, PeanoNat.Nat.add_0_r.
          pose proof remaining_le_full_length inp (lk_dir lk).
          assert (remaining_length inp (lk_dir lk) * expanded_size r0 <= length (input_str inp) * expanded_size r0). {
            apply PeanoNat.Nat.mul_le_mono_r. auto.
          }
          unfold actions_fuel_nolk in FUEL. simpl in FUEL.
          destruct first_check_input; lia.
        }
        assert (forall gmlk, compute_result rer cont inp gmlk dir fuel <> Out_of_fuel). {
          intros gmlk. apply IHfuel.
          1: eapply afr_pop_lk_cont; eauto.
          unfold actions_fuel in *. simpl actions_lookaround_fuel in FUEL.
          unfold actions_fuel_nolk in FUEL. simpl first_check_input in FUEL.
          destruct (first_check_input cont) as [inpchk|] eqn:FSTCHK.
          - pose proof actions_fuel_nolk_notlast_le inp cont inpchk dir FSTCHK.
            simpl in FUEL. rewrite FSTCHK in FUEL.
            lia.
          - unfold actions_fuel_nolk. rewrite FSTCHK. simpl in FUEL. lia.
        }
        destruct compute_result as [| |[reslk gmlk]] eqn:C; try contradiction;
          destruct compute_result; try contradiction;
          destruct positivity; auto; intros; discriminate.
      + (* Group *)
        assert (CONT: compute_result rer (Areg r0 :: Aclose id :: cont) inp (Groups.GroupMap.open (idx inp) id gm) dir fuel <> Out_of_fuel). {
          apply IHfuel.
          - apply afr_pop_group. auto.
          - unfold actions_fuel, actions_fuel_nolk in FUEL. simpl first_check_input in FUEL.
            destruct first_check_input as [inpchk|] eqn:FSTCHK.
            + simpl in FUEL.
              pose proof actions_fuel_nolk_notlast_le inp (Areg r0 :: Aclose id :: cont) inpchk dir FSTCHK.
              simpl in H. rewrite FSTCHK in FUEL, H.
              unfold actions_fuel. simpl actions_lookaround_fuel. lia.
            + unfold actions_fuel, actions_fuel_nolk. setoid_rewrite FSTCHK.
              simpl actions_lookaround_fuel.
              unfold gt in *.
              simpl chunk_size in *. simpl actions_lookaround_fuel in FUEL. lia.
        }
        destruct compute_result; try contradiction; auto.
      +
        destruct anchor_satisfied; try discriminate.
        assert (CONT: compute_result rer cont inp gm dir fuel <> Out_of_fuel). {
          apply IHfuel.
          - apply afr_pop_anchor with (a := a). auto.
          - unfold actions_fuel, actions_fuel_nolk in FUEL. simpl first_check_input in FUEL.
            destruct first_check_input as [inpchk|] eqn:FSTCHK.
            + simpl in FUEL. rewrite FSTCHK in FUEL. pose proof actions_fuel_nolk_notlast_le inp cont inpchk dir FSTCHK.
              unfold actions_fuel. lia.
            + unfold actions_fuel, actions_fuel_nolk. rewrite FSTCHK. simpl chunk_size in FUEL.
              simpl actions_lookaround_fuel in FUEL. lia.
        }
        destruct compute_result; try contradiction; auto.
      + (* Backreference *)
        destruct read_backref as [[br_str nextinp]| ] eqn:READ; try discriminate.
        assert (CONT: compute_result rer cont nextinp gm dir fuel <> Out_of_fuel). {
          pose proof read_backref_advance_input_n rer gm id inp br_str nextinp dir READ as [n H]. apply IHfuel.
          - eapply afr_pop_backref. + eauto. + symmetry. apply H. (* The backreference read succeeds, hence nextinp = advance_input n inp for some n *)
          - symmetry in H. pose proof read_backref_decreases_fuel inp id n nextinp cont dir H.
            lia.
        }
        destruct compute_result; try contradiction; auto.
      +
        destruct is_strict_suffix eqn:SS; try discriminate.
        assert (CONT: compute_result rer cont inp gm dir fuel <> Out_of_fuel). {
          apply IHfuel.
          - apply afr_pop_check with (inpcheck := inpcheck). + apply is_strict_suffix_correct. auto. + auto.
          - unfold actions_fuel, actions_fuel_nolk in FUEL. simpl first_check_input in FUEL.
            cbv match in FUEL.
            unfold actions_fuel, actions_fuel_nolk. simpl in FUEL.
            (* AFR implies that cont must start with a quantifier *)
            pose proof afr_checks_fby_quant r inp (Acheck inpcheck :: cont) dir AFR as CHK_FBY_QUANT.
            unfold checks_fby_quant in CHK_FBY_QUANT. specialize (CHK_FBY_QUANT 0 inpcheck eq_refl).
            destruct CHK_FBY_QUANT as [greedy [delta [rquant CHK_FBY_QUANT]]].
            destruct cont as [|a cont].
            1: { exfalso. discriminate. }
            destruct a as [rsub | ? | ?]. 2,3: exfalso; discriminate.
            destruct rsub. 1-4,6-9: exfalso; discriminate.
            simpl in CHK_FBY_QUANT. injection CHK_FBY_QUANT as -> -> -> ->.
            simpl first_check_input. destruct first_check_input as [inpchknext | ] eqn:SNDCHK.
            + (* NON-TRIVIAL: is_strict_suffix inp inpcheck forward = true implies
              is_strict_suffix inp inpchknext forward = true *)
              replace (is_strict_suffix inp inpchknext dir) with true.
              2: {
                symmetry. apply is_strict_suffix_correct.
                apply is_strict_suffix_correct in SS.
                pose proof afr_checks_ordered r inp _ dir AFR as ORDERED. simpl in ORDERED.
                pose proof actions_checks_first_check_input cont inpchknext SNDCHK. destruct H as [tl H].
                rewrite H in ORDERED.
                inversion ORDERED. subst a l.
                inversion H2. subst a l.
                inversion H5. subst b l.
                unfold input_le in H1. destruct H1 as [H1 | H1].
                - rewrite <- H1. auto.
                - eauto using strict_suffix_trans.
              }
              rewrite SS in FUEL. lia.
            + rewrite SS in FUEL. simpl in *. rewrite SNDCHK in FUEL. simpl in *. lia.
        }
        destruct compute_result; try contradiction; auto.
      +
        assert (CONT: compute_result rer cont inp (Groups.GroupMap.close (idx inp) gid gm) dir fuel <> Out_of_fuel). {
          apply IHfuel.
          - apply afr_pop_close with (gid := gid). auto.
          - unfold actions_fuel, actions_fuel_nolk in FUEL. simpl first_check_input in FUEL.
            destruct first_check_input as [inpchk|] eqn:FSTCHK.
            + pose proof actions_fuel_nolk_notlast_le inp cont inpchk dir FSTCHK. simpl in FUEL. rewrite FSTCHK in FUEL.
              unfold actions_fuel. lia.
            + unfold actions_fuel, actions_fuel_nolk. rewrite FSTCHK. simpl in *. lia.
        }
        destruct compute_result; try contradiction; auto.
  Qed.

  Corollary compute_result_spec:
    forall (r: regex) (inp: input) (act: actions) (dir: Direction),
      act_from_regex r inp act dir ->
      forall fuel, fuel > actions_fuel inp act dir ->
        forall gm rer t, is_tree rer act inp gm dir t ->
          res_to_leaf (compute_result rer act inp gm dir fuel) = Some (tree_res t gm inp dir).
  Proof.
    intros r inp act dir AFR fuel FUEL gm rer t TREE.
    pose proof result_terminates' r inp act dir AFR fuel FUEL gm rer as NOOF.
    destruct (compute_result rer act inp gm dir fuel) eqn:CR; [contradiction| |];
      (apply f_equal with (f := res_to_leaf) in CR;
       apply compute_result_is_tree in CR as [t' [IT LF]];
       assert (t' = t) by (eapply is_tree_determ; eauto); subst;
       cbn [res_to_leaf] in *; rewrite LF; reflexivity).
  Qed.

  (* removed the deprecated tree depth proofs *)

  Lemma regex_lookaround_fuel_bound:
    forall r str, regex_lookaround_fuel str r <= (1 + length str) * expanded_size r * expanded_size r.
  Proof.
    intros r str. induction r; simpl; lia.
  Qed.

  Theorem poly_fuel:
    forall inp r,
      actions_fuel inp [Areg r] forward <= (1 + remaining_length inp forward) * expanded_size r + (1 + length (input_str inp)) * expanded_size r * expanded_size r.
  Proof.
    intros inp r.
    unfold actions_fuel, actions_fuel_nolk.
    simpl first_check_input. cbv match. simpl chunk_size.
    rewrite PeanoNat.Nat.add_0_r.
    apply PeanoNat.Nat.add_le_mono_l.
    unfold actions_lookaround_fuel. rewrite PeanoNat.Nat.max_0_r.
    apply regex_lookaround_fuel_bound.
  Qed.

End MembershipProof.


Section PSPACE_algo.

  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).

  Definition pspace_algo (r:regex) (s:LWParameters.string) :=
    let init_fuel := S (actions_fuel (init_input s) [Areg r] forward) in
    match compute_result rer [Areg r] (init_input s) GroupMap.empty forward init_fuel with
    | Success _ => Some true
    | NoMatch => Some false
    | Out_of_fuel => None
    end.

  Theorem pspace_algo_true_correct:
    forall r s tree,
      is_tree rer [Areg r] (init_input s) GroupMap.empty forward tree ->
      pspace_algo r s = Some true <-> exists leaf, first_leaf tree (init_input s) = Some leaf.
  Proof.
    intros r s tree H. unfold first_leaf. split; intros.
    - unfold pspace_algo in H0.
      destruct compute_result eqn:CR; try solve [inversion H0].
      apply f_equal with (f:=res_to_leaf) in CR.
      apply compute_result_is_tree in CR. destruct CR as [t [IT LF]].
      assert (t = tree) by (eapply is_tree_determ; eauto). subst.
      eexists; eauto.
    - set (f:=S (actions_fuel (init_input s) [Areg r] forward)).
      assert (MORE: f > actions_fuel (init_input s) [Areg r] forward) by lia.
      unfold pspace_algo. destruct compute_result eqn:CR; auto.
      + specialize (result_terminates' r (init_input s) [Areg r] forward (afr_refl r _ _) f MORE GroupMap.empty rer) as OOF.
        subst f. rewrite CR in OOF. exfalso. apply OOF. auto.
      + apply f_equal with (f:=res_to_leaf) in CR.
        apply compute_result_is_tree in CR. destruct CR as [t [IT LF]].
        assert (t = tree) by (eapply is_tree_determ; eauto). subst.
        destruct H0 as [l TR]. rewrite TR in LF. inversion LF.
  Qed.

  Theorem pspace_algo_false_correct:
    forall r s tree,
      is_tree rer [Areg r] (init_input s) GroupMap.empty forward tree ->
      pspace_algo r s = Some false <-> first_leaf tree (init_input s) = None.
  Proof.
    intros r s tree H. unfold first_leaf. split; intros.
    - unfold pspace_algo in H0.
      destruct compute_result eqn:CR; try solve [inversion H0].
      apply f_equal with (f:=res_to_leaf) in CR.
      apply compute_result_is_tree in CR. destruct CR as [t [IT LF]].
      assert (t = tree) by (eapply is_tree_determ; eauto). subst. auto.
    - set (f:=S (actions_fuel (init_input s) [Areg r] forward)).
      assert (MORE: f > actions_fuel (init_input s) [Areg r] forward) by lia.
      unfold pspace_algo. destruct compute_result eqn:CR; auto.
      + specialize (result_terminates' r (init_input s) [Areg r] forward (afr_refl r _ _) f MORE GroupMap.empty rer) as OOF.
        subst f. rewrite CR in OOF. exfalso. apply OOF. auto.
      + apply f_equal with (f:=res_to_leaf) in CR.
        apply compute_result_is_tree in CR. destruct CR as [t [IT LF]].
        assert (t = tree) by (eapply is_tree_determ; eauto). subst.
        rewrite H0 in LF. inversion LF.
  Qed.

End PSPACE_algo.
