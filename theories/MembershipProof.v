From Linden Require Import Semantics Chars StrictSuffix FunctionalSemantics Tactics Tree
  FunctionalUtils ComputeIsTree Semantics.Tree Semantics.Groups.
From JsRegexOptp Require Export Basics.
From Warblre Require Import Base spec.RegExpRecord Notations.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations.

Section PSPACE_algo.

  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).

  Inductive match_result :=
  | Out_of_fuel: match_result
  | NoMatch: match_result
  | Success: leaf -> match_result.

  Fixpoint pspace_algo (act: actions) (inp: input) (gm: group_map) (dir: Direction) (fuel: nat): match_result :=
    match fuel with
    | 0 => Out_of_fuel
    | S fuel =>
        match act with
        | [] => Success (inp, gm)
        | Acheck strcheck :: cont =>
            if (is_strict_suffix inp strcheck dir) then
              pspace_algo cont inp gm dir fuel
            else NoMatch
        | Aclose gid :: cont =>
            pspace_algo cont inp (GroupMap.close (idx inp) gid gm) dir fuel
        | Areg Epsilon::cont => pspace_algo cont inp gm dir fuel
        | Areg (Regex.Character cd)::cont =>
            match read_char rer cd inp dir with
            | Some (c, nextinp) =>
                pspace_algo cont nextinp gm dir fuel
            | None => NoMatch
            end
        (* tree_disj *)
        | Areg (Disjunction r1 r2)::cont =>
            match pspace_algo (Areg r1 :: cont) inp gm dir fuel with
            | Out_of_fuel => Out_of_fuel
            | Success lf => Success lf
            | NoMatch => pspace_algo (Areg r2 :: cont) inp gm dir fuel
            end
        | Areg (Sequence r1 r2)::cont =>
            pspace_algo (seq_list r1 r2 dir ++ cont) inp gm dir fuel
        (* tree_quant_forced *)
        | Areg (Quantified greedy (S min) delta r1)::cont =>
            let gidl := def_groups r1 in
            pspace_algo (Areg r1 :: Areg (Quantified greedy min delta r1) :: cont) inp (GroupMap.reset gidl gm) dir fuel
        (* tree_quant_done *)
        | Areg (Quantified greedy 0 (NoI.N 0) r1)::cont =>
            pspace_algo cont inp gm dir fuel
        (* tree_quant_free *)
        | Areg (Quantified greedy 0 delta r1)::cont =>
            let gidl := def_groups r1 in
            match greedy with
            | true =>
                match (pspace_algo (Areg r1 :: Acheck inp :: Areg (Quantified greedy 0 (noi_pred delta) r1) :: cont) inp (GroupMap.reset gidl gm) dir fuel) with
                | Out_of_fuel => Out_of_fuel
                | Success lf => Success lf
                | NoMatch => pspace_algo cont inp gm dir fuel
                end
            | false =>
                match (pspace_algo cont inp gm dir fuel) with
                | Out_of_fuel => Out_of_fuel
                | Success lf => Success lf
                | NoMatch => (pspace_algo (Areg r1 :: Acheck inp :: Areg (Quantified greedy 0 (noi_pred delta) r1) :: cont) inp (GroupMap.reset gidl gm) dir fuel)
                end
            end
        | Areg (Group gid r1)::cont =>
            pspace_algo (Areg r1 :: Aclose gid :: cont) inp (GroupMap.open (idx inp) gid gm) dir fuel
        (* tree_lk, tree_lk_fail *)
        | Areg (Lookaround lk r1)::cont =>
            match (pspace_algo [Areg r1] inp gm (lk_dir lk) fuel) with
            | Out_of_fuel => Out_of_fuel
            | Success (_,gmlk) =>
                match (positivity lk) with
                | false => NoMatch
                | true => pspace_algo cont inp gmlk dir fuel
                end
            | NoMatch =>
                match (positivity lk) with
                | true => NoMatch
                | false => pspace_algo cont inp gm dir fuel
                end
            end
        | Areg (Anchor a)::cont =>
            if anchor_satisfied rer a inp then
              pspace_algo cont inp gm dir fuel
            else NoMatch
        | Areg (Backreference gid)::cont =>
          match read_backref rer gm gid inp dir with
          | Some (br_str, nextinp) =>
            pspace_algo cont nextinp gm dir fuel
          | None => NoMatch
          end
        end
    end.

  Definition res_to_leaf (mr: match_result) : option (option leaf) :=
    match mr with
    | Out_of_fuel => None
    | NoMatch => Some None
    | Success lf => Some (Some lf)
    end.

  Theorem pspace_algo_correctness:
    forall fuel act inp gm dir t,
      compute_tree rer act inp gm dir fuel = Some t ->
      res_to_leaf (pspace_algo act inp gm dir fuel) = Some (tree_res t gm inp dir).
  Proof.
    induction fuel as [|fuel IH]; [discriminate|]; intros act inp gm dir t H.
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

End PSPACE_algo.

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

  (* Roughly: the cost of an additional iteration. *)
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
    | Lookaround _ r1 => (* the initial fuel of that search ([actions_fuel_init]) *)
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
    intros ? ? OK. induction OK as [|a ? _ OK ?]; [reflexivity|].
    pose proof all_suffixes_hd OK. destruct a; simpl in *; nia.
  Qed.

  Lemma expanded_size_pos: forall r, 1 <= expanded_size r.
  Proof. induction r; simpl; nia. Qed.

  Lemma length_le_actions_size: forall act, length act <= actions_size act.
  Proof.
    induction act as [|[r| |] l IH]; simpl; try pose proof (expanded_size_pos r); lia.
  Qed.

  Corollary actions_size_bound':
    forall {r dir act}, act_from_regex r dir act ->
      let n := expanded_size r in actions_size act <= n + Nat.div2 (n * S n).
  Proof.
    intros r ? ? AFR. cbv zeta. pose proof (chunk_bound AFR) as OK.
    pose proof all_suffixes_hd OK. pose proof actions_size_le (expanded_size r) OK.
    unfold chunk_ok in *. pose proof triangle_even (expanded_size r). nia.
  Qed.

  Corollary actions_length_bound:
    forall {r dir act}, act_from_regex r dir act ->
      let n := expanded_size r in length act <= n + Nat.div2 (n * S n).
  Proof.
    intros * AFR. pose proof length_le_actions_size act.
    pose proof (actions_size_bound' AFR). cbv zeta in *. lia.
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
    pose proof Nat.le_max_l (regex_lookaround_fuel (input_str inp) (Lookaround lk rlk))
      (actions_lookaround_fuel (input_str inp) cont).
    unfold actions_fuel, spare. simpl. unfold core_size in *. nia.
  Qed.

  Theorem fuel_decreases: forall {r dir act inp act' inp'},
      act_from_regex r dir act -> act_step dir act inp act' inp' ->
      actions_fuel r inp' act' dir < actions_fuel r inp act dir.
  Proof.
    intros * AFR%iter_bound STEP. destruct STEP;
      pose proof (all_suffixes_hd AFR);
      pose proof (all_suffixes_hd (all_suffixes_tl AFR));
      try pose proof (skip_size_pos rsub);
      (apply fuel_same + eapply fuel_advance).
    all: try eauto using strict_suffix_samestr, strict_suffix_remaining.
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
    induction fuel as [|fuel IHfuel]; [lia|]. intros r inp act dir AFR FUEL gm rer. simpl.
    assert (REC: forall act' inp' gm', act_step dir act inp act' inp' ->
                   compute_tree rer act' inp' gm' dir fuel <> None)
      by (intros * STEP; pose proof (fuel_decreases AFR STEP); eauto using afr_step).
    assert (RECLK: forall rlk dir' gm',
               actions_fuel rlk inp [Areg rlk] dir' < actions_fuel r inp act dir ->
               compute_tree rer [Areg rlk] inp gm' dir' fuel <> None)
      by eauto using afr_refl.
    clear IHfuel AFR FUEL.
    destruct act as [ | [ [ | | | | ? min delta | ? rlk | | | ] | | ] cont ].
    + discriminate.
    + recurse REC.
    + destruct read_char as [[? ?]|] eqn:READ; try discriminate. recurse REC.
    + repeat recurse REC.
    + recurse REC.
    +
      destruct min as [|min]; [destruct delta as [[|]|]|]; repeat recurse REC.
    +
      recurse RECLK. destruct lk_result; try discriminate. recurse REC.
    + recurse REC.
    + destruct anchor_satisfied; try discriminate. recurse REC.
    +
      destruct read_backref as [[br_str ?]|] eqn:READ; try discriminate.
      apply read_backref_success_advance in READ as ->.
      destruct (advance_input_n_suffix inp (length br_str) dir _ eq_refl) as [->|?];
        recurse REC.
    + destruct is_strict_suffix eqn:SS; try discriminate. recurse REC.
    + recurse REC.
  Qed.

  Lemma compute_tree_of_is_tree: forall {r dir act inp gm rer t fuel},
      act_from_regex r dir act -> fuel > actions_fuel r inp act dir ->
      is_tree rer act inp gm dir t -> compute_tree rer act inp gm dir fuel = Some t.
  Proof.
    intros * AFR FUEL TREE; pose proof functional_terminates' _ inp AFR FUEL gm rer.
    destruct compute_tree as [t'|] eqn:?; [|congruence].
    f_equal; eauto using compute_is_tree, is_tree_determ.
  Qed.

  Theorem algo_terminates:
    forall (r: regex) (inp: input) (act: actions) (dir: Direction),
      act_from_regex r dir act ->
      forall fuel, fuel > actions_fuel r inp act dir ->
        forall gm rer, pspace_algo rer act inp gm dir fuel <> Out_of_fuel.
  Proof.
    intros ? inp act dir AFR fuel FUEL gm rer.
    destruct (compute_tree rer act inp gm dir fuel) eqn:TREE.
    - apply pspace_algo_correctness in TREE. destruct pspace_algo; simpl in TREE; congruence.
    - exfalso. exact (functional_terminates' fuel inp AFR FUEL gm rer TREE).
  Qed.

  Corollary algo_terminates_regex:
    forall (r: regex) (inp: input) rer,
      pspace_algo rer [Areg r] inp GroupMap.empty forward
        (S (actions_fuel r inp [Areg r] forward)) <> Out_of_fuel.
  Proof. eauto using algo_terminates, afr_refl. Qed.

  (* TODO: are tree_depth, fuel_depth_bound, tree_depth_bound_act and
     tree_depth_bound_regex needed? *)
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
    induction fuel as [|fuel IH]; [discriminate|]; intros rer act inp gm dir t H.
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
    intros.
    eauto using fuel_depth_bound, compute_tree_of_is_tree, Nat.lt_succ_diag_r.
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
    intros r inp.
    assert (regex_lookaround_fuel (input_str inp) r <= (1 + length (input_str inp)) * lk_weight r)
      by (induction r; simpl; unfold core_size; nia).
    rewrite actions_fuel_init. lia.
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
    intros r ? inp ? ? TREE.
    pose proof tree_depth_bound_act r inp (afr_refl r forward) TREE.
    pose proof poly_fuel_linear r inp. lia.
  Qed.

End MembershipProof.
