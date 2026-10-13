From Linden Require Import Regex Parameters Semantics Chars StrictSuffix
  FunctionalSemantics Tactics Tree FunctionalUtils ComputeIsTree
  Semantics.Tree Semantics.Groups.
From JSRegexComplexity Require Export Basics.
From Warblre Require Import Base spec.RegExpRecord Notations.
From Stdlib Require Import List Lia PeanoNat.
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

  Theorem compute_result_correctness:
    forall fuel act inp gm dir t,
      compute_tree rer act inp gm dir fuel = Some t ->
      res_to_leaf (compute_result act inp gm dir fuel) = Some (tree_res t gm inp dir).
  Proof.
    induction fuel as [|fuel IH]; [discriminate|]; intros * H.
    repeat match goal with
            | _ => progress (simpl in *; unfold lk_result in *)
            | [ E: read_char _ _ _ _ = Some _ |- _ ] =>
                apply read_char_success_advance, advance_input_success in E
            | [ E: read_backref _ _ _ _ _ = Some _ |- _ ] => apply read_backref_success_advance in E
            | [ E: compute_tree _ _ _ _ _ _ = Some _ |- _ ] => apply IH in E
            | [ E: Some _ = Some _ |- _ ] => injection E as <-
            | [ E: context[match ?x with _ => _ end] |- _ ] => destruct x eqn:?; try discriminate
            | [ |- context[match ?x with _ => _ end] ] => destruct x eqn:?; try discriminate
            end;
    solve [reflexivity | congruence].
  Qed.

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

  Corollary compute_result_is_tree_same_leaf:
    forall fuel act inp gm dir leaf t,
      res_to_leaf (compute_result act inp gm dir fuel) = Some leaf ->
      is_tree rer act inp gm dir t ->
      tree_res t gm inp dir = leaf.
  Proof.
    intros fuel act inp gm dir leaf t H H0.
    apply compute_result_is_tree in H as [tree [IT LF]].
    eapply is_tree_determ with (t2:=tree) in H0; auto. subst. auto.
  Qed.


End ComputeResult.

Section MembershipProof.
  Context {params: LindenParameters}.

  Local Hint Extern 1 (_ < _) => lia : core.

  Fixpoint skip_size (r: regex): nat := match r with
  | Epsilon | Regex.Character _ => 1
  | Disjunction r1 r2 | Sequence r1 r2 => 1 + skip_size r1 + skip_size r2
  | Quantified _ min _ r1 => 1 + min * (1 + skip_size r1)
  | Lookaround _ _ => 1
  | Group _ r1 => 2 + skip_size r1
  | Anchor _ | Backreference _ => 1
  end.

  Fixpoint iter_size (r: regex): nat := match r with
  | Epsilon | Regex.Character _ => 0
  | Disjunction r1 r2 | Sequence r1 r2 => iter_size r1 + iter_size r2
  | Quantified _ min _ r1 => 2 + skip_size r1 + iter_size r1 + min * (2 + iter_size r1)
  | Lookaround _ _ => 0
  | Group _ r1 => iter_size r1
  | Anchor _ | Backreference _ => 0
  end.

  Definition core_size (r: regex): nat := skip_size r + iter_size r.

  Lemma skip_size_pos: forall r, 1 <= skip_size r.
  Proof. destruct r; simpl; lia. Qed.

  (* `act_step dir act inp act' inp'` over-approximates when the semantic
  state (inp, act, dir) can step to (inp', act', dir). *)
  Inductive act_step (dir: Direction): actions -> input -> actions -> input -> Prop :=
  | ast_drop: forall rsub l inp,
      act_step dir (Areg rsub :: l) inp l inp
  | ast_close: forall gid l inp,
      act_step dir (Aclose gid :: l) inp l inp
  | ast_check: forall p l inp,
      is_strict_suffix inp p dir = true ->
      act_step dir (Acheck p :: l) inp l inp
  | ast_read: forall rsub l inp inp',
      strict_suffix inp' inp dir ->
      act_step dir (Areg rsub :: l) inp l inp'
  | ast_disj_l: forall r1 r2 l inp,
      act_step dir (Areg (Disjunction r1 r2) :: l) inp (Areg r1 :: l) inp
  | ast_disj_r: forall r1 r2 l inp,
      act_step dir (Areg (Disjunction r1 r2) :: l) inp (Areg r2 :: l) inp
  | ast_seq: forall r1 r2 l inp,
      act_step dir (Areg (Sequence r1 r2) :: l) inp (seq_list r1 r2 dir ++ l) inp
  | ast_quant_forced: forall greedy min delta r1 l inp,
      act_step dir (Areg (Quantified greedy (S min) delta r1) :: l) inp
        (Areg r1 :: Areg (Quantified greedy min delta r1) :: l) inp
  | ast_quant_iter: forall greedy delta r1 l inp,
      act_step dir (Areg (Quantified greedy 0 delta r1) :: l) inp
        (Areg r1 :: Acheck inp :: Areg (Quantified greedy 0 (noi_pred delta) r1) :: l) inp
  | ast_group: forall gid r1 l inp,
      act_step dir (Areg (Group gid r1) :: l) inp (Areg r1 :: Aclose gid :: l) inp.

  Inductive act_from_regex (r: regex) (dir: Direction): actions -> Prop :=
  | afr_refl: act_from_regex r dir [Areg r]
  | afr_step: forall act inp act' inp',
      act_from_regex r dir act -> act_step dir act inp act' inp' ->
      act_from_regex r dir act'.

  Fixpoint act_wt (w: regex -> nat) (wc: nat) (act: actions): nat :=
    match act with
    | [] => 0
    | Areg r :: l => w r + act_wt w wc l
    | Acheck _ :: l | Aclose _ :: l => wc + act_wt w wc l
    end.

  Notation skip_wt := (act_wt skip_size 1).
  Notation actions_size := (act_wt expanded_size 1).

  Fixpoint first_chunk (act: actions): actions :=
    match act with
    | Acheck _ :: _ | [] => []
    | a :: l => a :: first_chunk l
    end.

  Notation iter_chunk l := (act_wt iter_size 0 (first_chunk l)).

  Fixpoint first_check_passes (dir: Direction) (inp: input) (act: actions): bool :=
    match act with
    | [] => true
    | Acheck p :: _ => is_strict_suffix inp p dir
    | _ :: l => first_check_passes dir inp l
    end.

  Fixpoint regex_lookaround_fuel (str: LWParameters.string) (r: regex): nat :=
    match r with
    | Epsilon | Regex.Character _ => 0
    | Disjunction r1 r2 | Sequence r1 r2 => max (regex_lookaround_fuel str r1) (regex_lookaround_fuel str r2)
    | Quantified _ _ _ r1 => regex_lookaround_fuel str r1
    | Lookaround _ r1 =>
        iter_size r1 * length str + core_size r1 + regex_lookaround_fuel str r1
    | Group _ r1 => regex_lookaround_fuel str r1
    | Anchor _ | Backreference _ => 0
    end.

  Fixpoint actions_lookaround_fuel (str: LWParameters.string) (act: actions): nat :=
    match act with
    | [] => 0
    | Areg rsub :: l => max (regex_lookaround_fuel str rsub) (actions_lookaround_fuel str l)
    | Acheck _ :: l | Aclose _ :: l => actions_lookaround_fuel str l
    end.

  Definition spare (r: regex) (inp: input) (act: actions) (dir: Direction): nat :=
    if first_check_passes dir inp act then iter_size r else iter_chunk act.

  Definition actions_fuel (r: regex) (inp: input) (act: actions) (dir: Direction): nat :=
    iter_size r * remaining_length inp dir
    + skip_wt act
    + spare r inp act dir
    + actions_lookaround_fuel (input_str inp) act.

  Local Arguments Nat.max : simpl never.

  Fixpoint num_checks (act: actions): nat :=
    match act with
    | [] => 0
    | Acheck _ :: l => 1 + num_checks l
    | _ :: l => num_checks l
    end.

  Definition iter_ok (r: regex) (act: actions): Prop :=
    iter_chunk act <= iter_size r.

  Definition chunk_ok (r: regex) (act: actions): Prop :=
    num_checks act + actions_size (first_chunk act) <= expanded_size r.

  Local Ltac inv_case :=
    repeat apply as_cons; try apply as_nil;
    try match goal with
        | [ IH: all_suffixes _ _ |- _ ] =>
            first [exact (all_suffixes_tl IH) | apply all_suffixes_hd in IH]
        end;
    unfold iter_ok, chunk_ok in *; simpl in *; lia.

  Lemma iter_bound: forall {r dir act},
    act_from_regex r dir act -> all_suffixes (iter_ok r) act.
  Proof. induction 1 as [|???? _ IH STEP]; [|destruct STEP]; destruct dir; inv_case. Qed.

  Lemma chunk_bound: forall {r dir act},
    act_from_regex r dir act -> all_suffixes (chunk_ok r) act.
  Proof. induction 1 as [|???? _ IH STEP]; [|destruct STEP]; destruct dir; inv_case. Qed.

  Lemma actions_size_le:
    forall n {act}, all_suffixes (fun l => num_checks l + actions_size (first_chunk l) <= n) act ->
      2 * actions_size act + num_checks act * num_checks act
      <= 2 * actions_size (first_chunk act) + num_checks act * (2 * n + 3).
  Proof.
    induction 1 as [|a ? _ OK]; [reflexivity|].
    pose proof all_suffixes_hd OK. destruct a; simpl in *; nia.
  Qed.

  Lemma length_le_actions_size: forall act, length act <= actions_size act.
  Proof.
    induction act as [|[r| |] l IH]; simpl; try pose proof (expanded_size_pos r); lia.
  Qed.

  Corollary actions_size_bound:
    forall {r dir act}, act_from_regex r dir act ->
      let n := expanded_size r in actions_size act <= n + Nat.div2 (n * S n).
  Proof.
    intros * OK%chunk_bound; cbv zeta.
    pose proof all_suffixes_hd OK; pose proof actions_size_le (expanded_size r) OK.
    unfold chunk_ok in *; pose proof triangle_even (expanded_size r); nia.
  Qed.

  Lemma act_step_length dir act inp act' inp':
      act_step dir act inp act' inp' ->
      length act' <= 2 + length act.
  Proof. inversion 1; subst; cbn; unfold seq_list; try destruct dir; cbn; lia. Qed.

  Lemma lk_size_bound {r dir act}:
      act_from_regex r dir act ->
      forall lk rlk, In (Areg (Lookaround lk rlk)) act ->
                     S (expanded_size rlk) <= expanded_size r.
  Proof.
    intros OK%chunk_bound lk rlk IN; induction OK as [|? ? CH]; [contradiction|].
    destruct IN as [->|]; [unfold chunk_ok in CH; simpl in CH; lia | auto].
  Qed.

  Definition sz_bound (n: nat) := n + Nat.div2 (n * S n).

  Lemma sz_bound_mono n m: n <= m -> sz_bound n <= sz_bound m.
  Proof.
    intro; unfold sz_bound; pose proof triangle_even n; pose proof triangle_even m; nia.
  Qed.

  Inductive act_reachable (r: regex): Direction -> actions -> Prop :=
  | ar_top: forall dir act, act_from_regex r dir act -> act_reachable r dir act
  | ar_lk: forall dir lk rlk cont dir' act',
      act_reachable r dir (Areg (Lookaround lk rlk) :: cont) ->
      act_from_regex rlk dir' act' -> act_reachable r dir' act'.

  Lemma reachable_bound {r dir act}:
      act_reachable r dir act ->
      actions_size act <= sz_bound (expanded_size r) /\
      (forall lk rlk, In (Areg (Lookaround lk rlk)) act ->
                      S (expanded_size rlk) <= expanded_size r).
  Proof.
    induction 1 as [dir act AFR|dir lk rlk cont dir' act' ? [_ IHlk] AFR];
      pose proof actions_size_bound AFR as ACT; cbv zeta in ACT.
    - split; eauto using lk_size_bound.
    - pose proof IHlk lk rlk (or_introl eq_refl).
      pose proof sz_bound_mono (expanded_size rlk) (expanded_size r) ltac:(lia).
      unfold sz_bound in *; split; [lia | intros * IN%(lk_size_bound AFR); lia].
  Qed.

  Corollary actions_length_bound:
    forall {r dir act}, act_from_regex r dir act ->
      let n := expanded_size r in length act <= n + Nat.div2 (n * S n).
  Proof.
    intros * AFR%actions_size_bound; pose proof length_le_actions_size act; cbv zeta in *; lia.
  Qed.

  Lemma fuel_same: forall {r inp act act' dir},
      skip_wt act' + spare r inp act' dir < skip_wt act + spare r inp act dir ->
      actions_lookaround_fuel (input_str inp) act'
        <= actions_lookaround_fuel (input_str inp) act ->
      actions_fuel r inp act' dir < actions_fuel r inp act dir.
  Proof. unfold actions_fuel. lia. Qed.

  Lemma fuel_advance: forall {r inp inp' act act' dir},
      input_str inp' = input_str inp ->
      remaining_length inp' dir < remaining_length inp dir ->
      iter_ok r act' ->
      skip_wt act' < skip_wt act ->
      actions_lookaround_fuel (input_str inp) act'
        <= actions_lookaround_fuel (input_str inp) act ->
      actions_fuel r inp' act' dir < actions_fuel r inp act dir.
  Proof.
    intros * STR RL OK DISC LK. unfold actions_fuel, spare, iter_ok in *.
    rewrite STR. destruct (first_check_passes dir inp' act'); nia.
  Qed.

  Lemma fuel_lk: forall r rlk lk inp cont dir,
      actions_fuel rlk inp [Areg rlk] (lk_dir lk)
        < actions_fuel r inp (Areg (Lookaround lk rlk) :: cont) dir.
  Proof.
    intros. pose proof remaining_le_full_length inp (lk_dir lk).
    unfold actions_fuel, spare. simpl. unfold core_size in *. nia.
  Qed.

  Theorem fuel_decreases: forall {r dir act inp act' inp'},
      act_from_regex r dir act -> act_step dir act inp act' inp' ->
      actions_fuel r inp' act' dir < actions_fuel r inp act dir.
  Proof.
    intros * AFR%iter_bound STEP. destruct STEP;
      pose proof all_suffixes_hd AFR;
      pose proof all_suffixes_hd (all_suffixes_tl AFR);
      try pose proof skip_size_pos rsub;
      (apply fuel_same + eapply fuel_advance).
    all: eauto using strict_suffix_samestr, strict_suffix_remaining.
    all: destruct dir; unfold spare, iter_ok in *; simpl in *;
      rewrite ?is_strict_suffix_irrefl;
      repeat match goal with [ SS: is_strict_suffix _ _ _ = true |- _ ] => rewrite SS end;
      repeat destruct (first_check_passes _ _ _); lia.
  Qed.

  Local Ltac recurse REC :=
    match goal with
    | [ |- context[compute_tree ?rer ?act ?inp ?gm ?dir ?fuel] ] =>
        let E := fresh "E" in
        destruct (compute_tree rer act inp gm dir fuel) eqn:E;
        [ try discriminate
        | eapply REC in E;
          [contradiction | eauto using act_step, read_suffix, read_char_success_advance, fuel_lk] ]
    end.

  Theorem functional_terminates':
    forall (fuel: nat) {r: regex} (inp: input) {act: actions} {dir: Direction},
      act_from_regex r dir act -> fuel > actions_fuel r inp act dir ->
      forall gm rer, compute_tree rer act inp gm dir fuel <> None.
  Proof.
    induction fuel as [|fuel IHfuel]; [lia|]. intros * AFR FUEL gm rer. simpl.
    assert (REC: forall act' inp' gm', act_step dir act inp act' inp' ->
                   compute_tree rer act' inp' gm' dir fuel <> None)
      by (intros * STEP; pose proof fuel_decreases AFR STEP; eauto using afr_step).
    assert (RECLK: forall rlk dir' gm',
               actions_fuel rlk inp [Areg rlk] dir' < actions_fuel r inp act dir ->
               compute_tree rer [Areg rlk] inp gm' dir' fuel <> None)
      by eauto using afr_refl.
    clear IHfuel AFR FUEL.
    destruct act as [ | [ [ | | | | ? [|] [[|]|] | | | | ] | | ] cont ]; try discriminate.
    all: try solve [repeat recurse REC].
    - destruct read_char as [[? ?]|] eqn:READ; try discriminate. recurse REC.
    - recurse RECLK. destruct lk_result; try discriminate. recurse REC.
    - destruct anchor_satisfied; try discriminate. recurse REC.
    - destruct read_backref as [[br_str ?]|] eqn:READ; try discriminate.
      apply read_backref_success_advance in READ as ->.
      destruct (advance_input_n_suffix inp (length br_str) dir _ eq_refl) as [->|?];
        recurse REC.
    - destruct is_strict_suffix eqn:SS; try discriminate. recurse REC.
  Qed.

  Lemma compute_tree_of_is_tree: forall {r dir act inp gm rer t fuel},
      act_from_regex r dir act -> fuel > actions_fuel r inp act dir ->
      is_tree rer act inp gm dir t -> compute_tree rer act inp gm dir fuel = Some t.
  Proof.
    intros * AFR FUEL TREE; pose proof functional_terminates' fuel inp AFR FUEL gm rer.
    destruct compute_tree eqn:?; [f_equal; eauto using compute_is_tree, is_tree_determ | congruence].
  Qed.

  Theorem algo_terminates:
    forall (r: regex) (inp: input) (act: actions) (dir: Direction),
      act_from_regex r dir act ->
      forall fuel, fuel > actions_fuel r inp act dir ->
        forall gm rer, compute_result rer act inp gm dir fuel <> Out_of_fuel.
  Proof.
    intros * AFR fuel FUEL gm rer; pose proof functional_terminates' fuel inp AFR FUEL gm rer.
    destruct compute_tree eqn:TREE; [apply compute_result_correctness in TREE | congruence].
    destruct compute_result; simpl in TREE; congruence.
  Qed.

  Fixpoint tree_depth (t: tree): nat :=
    match t with
    | Mismatch | Match => 1
    | Choice t1 t2 => 1 + max (tree_depth t1) (tree_depth t2)
    | Read _ t | ReadBackRef _ t | Progress t | AnchorPass _ t
    | GroupAction _ t => 1 + tree_depth t
    | LK _ tlk t => 1 + max (tree_depth tlk) (tree_depth t)
    | LKFail _ tlk => 1 + tree_depth tlk
    end.

  Lemma fuel_depth_bound:
    forall fuel rer act inp gm dir t,
      compute_tree rer act inp gm dir fuel = Some t ->
      tree_depth t <= 2 * fuel.
  Proof.
    induction fuel as [|fuel IH]; [discriminate|]; intros * H.
    repeat match goal with
            | _ => progress simpl in *
            | [ E: compute_tree _ _ _ _ _ _ = Some _ |- _ ] => apply IH in E
            | [ E: Some _ = Some _ |- _ ] => injection E as <-
            | [ |- context[greedy_choice ?g _ _] ] => destruct g
            | [ E: context[match ?x with _ => _ end] |- _ ] => destruct x eqn:?; try discriminate
            end; lia.
  Qed.

  Corollary tree_depth_bound_act:
    forall (r: regex) (inp: input) {act: actions} {dir: Direction},
      act_from_regex r dir act ->
      forall {gm rer t}, is_tree rer act inp gm dir t ->
        tree_depth t <= 2 * (S (actions_fuel r inp act dir)).
  Proof.
    intros; eauto using fuel_depth_bound, compute_tree_of_is_tree, Nat.lt_succ_diag_r.
  Qed.

  Lemma actions_fuel_init:
    forall r inp dir,
      actions_fuel r inp [Areg r] dir =
        iter_size r * remaining_length inp dir + core_size r
        + regex_lookaround_fuel (input_str inp) r.
  Proof. intros. unfold actions_fuel, spare, core_size. simpl. lia. Qed.

  Fixpoint lk_weight (r: regex): nat :=
    match r with
    | Epsilon | Regex.Character _ | Anchor _ | Backreference _ => 0
    | Disjunction r1 r2 | Sequence r1 r2 => max (lk_weight r1) (lk_weight r2)
    | Quantified _ _ _ r1 | Group _ r1 => lk_weight r1
    | Lookaround _ r1 => core_size r1 + lk_weight r1
    end.

  Theorem poly_fuel:
    forall r inp,
      actions_fuel r inp [Areg r] forward <=
        iter_size r * remaining_length inp forward + core_size r
        + (1 + length (input_str inp)) * lk_weight r.
  Proof.
    intros r inp; rewrite actions_fuel_init.
    enough (regex_lookaround_fuel (input_str inp) r <= (1 + length (input_str inp)) * lk_weight r) by lia.
    induction r; simpl; unfold core_size; nia.
  Qed.

  Corollary poly_fuel_linear:
    forall r inp,
      actions_fuel r inp [Areg r] forward
      <= (1 + length (input_str inp)) * expanded_size r.
  Proof.
    intros r inp. assert (core_size r + lk_weight r <= expanded_size r)
      by (induction r; simpl; unfold core_size in *; nia).
    pose proof poly_fuel r inp. pose proof remaining_le_full_length inp forward.
    unfold core_size in *. nia.
  Qed.

  Corollary tree_depth_bound_regex:
    forall (r: regex) rer inp gm t, is_tree rer [Areg r] inp gm forward t ->
        tree_depth t <= 2 * (S ((1 + length (input_str inp)) * expanded_size r)).
  Proof.
    intros * TREE%(tree_depth_bound_act r inp (afr_refl r forward)).
    pose proof poly_fuel_linear r inp; lia.
  Qed.

  Theorem fuel_budget_adequate inp (r: regex):
      fuel_budget r inp > actions_fuel r inp [Areg r] forward.
  Proof. pose proof poly_fuel_linear r inp; unfold fuel_budget; lia. Qed.

  Corollary compute_result_budget:
    forall (r: regex) (inp: input) gm rer t,
      is_tree rer [Areg r] inp gm forward t ->
      res_to_leaf (compute_result rer [Areg r] inp gm forward (fuel_budget r inp))
      = Some (tree_res t gm inp forward).
  Proof.
    eauto using compute_result_correctness, compute_tree_of_is_tree,
      afr_refl, fuel_budget_adequate.
  Qed.
End MembershipProof.


Section PSPACE_algo.

  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).

  Definition pspace_algo (r:regex) (s:LWParameters.string) :=
    let init_fuel := fuel_budget r (init_input s) in
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
      eapply compute_result_is_tree_same_leaf in CR; eauto.
    - set (f:=fuel_budget r (init_input s)).
      assert (MORE: f > actions_fuel r (init_input s) [Areg r] forward)
        by eauto using fuel_budget_adequate.
      unfold pspace_algo. destruct compute_result eqn:CR; auto.
      + specialize (algo_terminates r (init_input s) [Areg r] forward (afr_refl r forward) f MORE GroupMap.empty rer) as OOF.
        subst f. rewrite CR in OOF. exfalso. apply OOF. auto.
      + apply f_equal with (f:=res_to_leaf) in CR.
        eapply compute_result_is_tree_same_leaf in CR; eauto.
        destruct H0 as [l TR]. rewrite TR in CR. inversion CR.
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
      eapply compute_result_is_tree_same_leaf in CR; eauto.
    - set (f:=fuel_budget r (init_input s)).
      assert (MORE: f > actions_fuel r (init_input s) [Areg r] forward)
        by eauto using fuel_budget_adequate.
      unfold pspace_algo. destruct compute_result eqn:CR; auto.
      + specialize (algo_terminates r (init_input s) [Areg r] forward (afr_refl r forward) f MORE GroupMap.empty rer) as OOF.
        subst f. rewrite CR in OOF. exfalso. apply OOF. auto.
      + apply f_equal with (f:=res_to_leaf) in CR.
        eapply compute_result_is_tree_same_leaf in CR; eauto.
        rewrite H0 in CR. inversion CR.
  Qed.

End PSPACE_algo.
