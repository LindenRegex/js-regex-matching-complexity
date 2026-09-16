(** * OptP membership for JavaScript regex matching without lookarounds *)

From Linden Require Import Semantics Chars StrictSuffix FunctionalSemantics Tree
  Semantics.Tree Semantics.Groups.
From Warblre Require Import Base spec.RegExpRecord.
From Stdlib Require Import List Lia.
Import ListNotations.
From JsRegexOptp Require Import MembershipProof Bits.
From JsRegexOptp Require Export Basics.

Section OptpAlgo.

  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).

  Record config := Cfg { cfg_act: actions; cfg_inp: input; cfg_gm: group_map }.

  Inductive step :=
  | SLeaf (lf: leaf)
  | SFail
  | SGo (c: config)
  | SBranch (hi lo: config).  (* two successors, [hi] the higher-priority one *)

  Definition optp_step (dir: Direction) (c: config): step :=
    match c with
    | Cfg act inp gm =>
        match act with
        | [] => SLeaf (inp, gm)
        | Acheck strcheck :: cont =>
            if is_strict_suffix inp strcheck dir then SGo (Cfg cont inp gm) else SFail
        | Aclose gid :: cont => SGo (Cfg cont inp (GroupMap.close (idx inp) gid gm))
        | Areg Epsilon :: cont => SGo (Cfg cont inp gm)
        | Areg (Regex.Character cd) :: cont =>
            match read_char rer cd inp dir with
            | Some (_, nextinp) => SGo (Cfg cont nextinp gm)
            | None => SFail
            end
        | Areg (Disjunction r1 r2) :: cont =>
            SBranch (Cfg (Areg r1 :: cont) inp gm) (Cfg (Areg r2 :: cont) inp gm)
        | Areg (Sequence r1 r2) :: cont => SGo (Cfg (seq_list r1 r2 dir ++ cont) inp gm)
        | Areg (Quantified greedy (S min) delta r1) :: cont =>
            SGo (Cfg (Areg r1 :: Areg (Quantified greedy min delta r1) :: cont) inp
                   (GroupMap.reset (def_groups r1) gm))
        | Areg (Quantified greedy 0 (NoI.N 0) r1) :: cont => SGo (Cfg cont inp gm)
        | Areg (Quantified greedy 0 delta r1) :: cont =>
            let iter := Cfg (Areg r1 :: Acheck inp ::
                               Areg (Quantified greedy 0 (noi_pred delta) r1) :: cont)
                          inp (GroupMap.reset (def_groups r1) gm) in
            let skip := Cfg cont inp gm in
            if greedy then SBranch iter skip else SBranch skip iter
        | Areg (Group gid r1) :: cont =>
            SGo (Cfg (Areg r1 :: Aclose gid :: cont) inp (GroupMap.open (idx inp) gid gm))
        | Areg (Lookaround _ _) :: cont => SFail
        | Areg (Anchor a) :: cont =>
            if anchor_satisfied rer a inp then SGo (Cfg cont inp gm) else SFail
        | Areg (Backreference gid) :: cont =>
            match read_backref rer gm gid inp dir with
            | Some (_, nextinp) => SGo (Cfg cont nextinp gm)
            | None => SFail
            end
        end
    end.

  (* [Out_of_fuel] means the guess was too short. *)
  Fixpoint optp_algo (dir: Direction) (c: config) (cs: list bool): match_result :=
    match cs with
    | [] => Out_of_fuel
    | b :: cs =>
        match optp_step dir c with
        | SLeaf lf => Success lf
        | SFail => NoMatch
        | SGo c' => optp_algo dir c' cs
        | SBranch hi lo => optp_algo dir (if b then hi else lo) cs
        end
    end.

  Fixpoint actions_no_lookaround (act: actions): Prop :=
    match act with
    | [] => True
    | Areg r :: act => no_lookaround r /\ actions_no_lookaround act
    | _ :: act => actions_no_lookaround act
    end.

  Lemma actions_no_lookaround_seq_list r1 r2 dir cont:
      no_lookaround r1 -> no_lookaround r2 -> actions_no_lookaround cont ->
      actions_no_lookaround (seq_list r1 r2 dir ++ cont).
  Proof. destruct dir; cbn; tauto. Qed.

  Definition optp_spec (n: nat) (res: list bool -> match_result) (o: option leaf): Prop :=
    (forall cs, length cs = n -> res cs <> Out_of_fuel) /\
    match o with
    | None => forall cs, length cs = n -> res cs = NoMatch
    | Some lf =>
        exists cs0, length cs0 = n /\ res cs0 = Success lf /\
                 forall cs, length cs = n -> res cs <> NoMatch -> bits_le cs cs0 = true
    end.

  Local Ltac guess :=
    intros [|[] cs] LEN; cbn in LEN; try discriminate; injection LEN as LEN.

  Lemma optp_spec_choice n res res1 res2 o1 o2:
      (forall cs, res (true :: cs) = res1 cs) ->
      (forall cs, res (false :: cs) = res2 cs) ->
      optp_spec n res1 o1 -> optp_spec n res2 o2 ->
      optp_spec (S n) res (seqop o1 o2).
  Proof.
    intros EL ER [NOF1 S1] [NOF2 S2].
    destruct o1 as [lf1|]; cbn [seqop]; (split; [guess; [rewrite EL | rewrite ER]; auto|]).
    - destruct S1 as (cs0 & LEN0 & SUCC & MAX); exists (true :: cs0); repeat split;
        [cbn; lia | now rewrite EL | guess; cbn; [rewrite EL|]; auto].
    - destruct o2 as [lf2|]; [|guess; [rewrite EL | rewrite ER]; auto].
      destruct S2 as (cs0 & LEN0 & SUCC & MAX); exists (false :: cs0); repeat split;
        [cbn; lia | now rewrite ER | guess; cbn; [now rewrite EL, S1 | rewrite ER; auto]].
  Qed.

  Lemma optp_spec_step n res res' o:
      (forall b cs, res (b :: cs) = res' cs) -> optp_spec n res' o -> optp_spec (S n) res o.
  Proof.
    intros; replace o with (seqop o o) by (now destruct o); eauto using optp_spec_choice.
  Qed.

  Definition res_of (o: option leaf): match_result :=
    match o with Some lf => Success lf | None => NoMatch end.

  Lemma optp_spec_const n o: optp_spec n (fun _ => res_of o) o.
  Proof.
    destruct o as [lf|]; split; intros; try discriminate; try reflexivity;
      exists (repeat true n); auto using repeat_length, bits_le_ones.
  Qed.

  Lemma optp_spec_done n res o:
      (forall b cs, res (b :: cs) = res_of o) -> optp_spec (S n) res o.
  Proof.
    intros; apply optp_spec_step with (res' := fun _ => res_of o); auto using optp_spec_const.
  Qed.

  Definition head_fuel (a: action): nat :=
    match a with
    | Areg (Quantified _ 0 _ _) => 1
    | Areg r => expanded_size r
    | Aclose _ => 1
    | Acheck _ => 0
    end.

  Definition not_check (a: action): Prop :=
    match a with Acheck _ => False | _ => True end.

  Lemma first_check_input_app pre cont:
    first_check_input pre = None ->
    first_check_input (pre ++ cont) = first_check_input cont.
  Proof.
    induction pre as [|[r|i|g] pre IH]; intro H; simpl in H |- *; auto; discriminate.
  Qed.

  Lemma chunk_size_app pre cont:
    first_check_input pre = None ->
    chunk_size (pre ++ cont) = chunk_size pre + chunk_size cont.
  Proof.
    induction pre as [|[r|i|g] pre IH]; intro H; simpl in H |- *;
      try discriminate; auto; rewrite IH by assumption; lia.
  Qed.

  Lemma actions_fuel'_app pre cont:
    first_check_input pre = None ->
    actions_fuel' (pre ++ cont) = chunk_size pre + actions_fuel' cont.
  Proof.
    induction pre as [|[r|i|g] pre IH]; intro H; simpl in H |- *;
      try discriminate; auto; rewrite IH by assumption; lia.
  Qed.

  Lemma last_chunk_size_cons a l inpchk:
    first_check_input (a :: l) = Some inpchk ->
    last_chunk_size (a :: l) = last_chunk_size l.
  Proof.
    destruct a as [r|ic|g]; intro H; cbn in H |- *; rewrite ?H; reflexivity.
  Qed.

  Lemma last_chunk_size_app pre cont inpchk:
    first_check_input pre = None ->
    first_check_input cont = Some inpchk ->
    last_chunk_size (pre ++ cont) = last_chunk_size cont.
  Proof.
    induction pre as [|[r|i|g] pre IH]; intros FSTPRE FSTCONT; cbn in FSTPRE |- *;
      [reflexivity | | discriminate |]; now rewrite first_check_input_app, FSTCONT, IH.
  Qed.

  Lemma actions_fuel_nolk_cons_ge inp a cont dir inpchk:
    not_check a ->
    first_check_input cont = Some inpchk ->
    actions_fuel_nolk inp (a :: cont) dir >=
      head_fuel a + actions_fuel' cont
      + ((if is_strict_suffix inp inpchk dir then 1 else 0)
         + remaining_length inp dir) * last_chunk_size cont.
  Proof.
    intros NOTCHK FSTCHK; unfold actions_fuel_nolk.
    destruct a as [r|ic|g]; [|contradiction|];
      cbn [first_check_input last_chunk_size]; rewrite FSTCHK; cbv match zeta;
      [destruct r|]; cbn [actions_fuel' head_fuel expanded_size]; try lia.
    destruct min; [destruct is_strict_suffix | cbn [expanded_size]]; lia.
  Qed.

  Lemma head_fuel_le a cont:
    not_check a -> head_fuel a + chunk_size cont <= chunk_size (a :: cont).
  Proof.
    intro NOTCHK; destruct a as [[|cd|r1 r2|r1 r2|g [|mn] d r1|lk r1|gid r1|anc|gid]|ic|g];
      cbn in *; lia.
  Qed.

  Lemma cons_decreases_fuel inp a new cont dir:
    not_check a ->
    first_check_input new = None ->
    chunk_size new < head_fuel a ->
    actions_lookaround_fuel (input_str inp) (new ++ cont)
      <= actions_lookaround_fuel (input_str inp) (a :: cont) ->
    actions_fuel inp (a :: cont) dir > actions_fuel inp (new ++ cont) dir.
  Proof.
    intros NOTCHK FSTNEW SIZE LKFUEL; unfold actions_fuel.
    apply PeanoNat.Nat.add_lt_le_mono; [|assumption].
    destruct (first_check_input cont) as [inpchk|] eqn:FSTCHK.
    - pose proof actions_fuel_nolk_cons_ge inp a cont dir inpchk NOTCHK FSTCHK as GE.
      pose proof actions_fuel_nolk_notlast_le inp (new ++ cont) inpchk dir
        (eq_trans (first_check_input_app new cont FSTNEW) FSTCHK) as LE.
      rewrite actions_fuel'_app, last_chunk_size_app with (inpchk := inpchk) in LE
        by assumption; lia.
    - destruct a as [r|ic|g]; [|contradiction|];
        unfold actions_fuel_nolk; cbn [first_check_input];
        rewrite first_check_input_app, FSTCHK, chunk_size_app by assumption;
        pose proof head_fuel_le _ cont NOTCHK; nia.
  Qed.

  Lemma lk_sub_decreases_fuel:
    forall inp lk r1 cont dir fuel,
      S fuel > actions_fuel inp (Areg (Lookaround lk r1) :: cont) dir ->
      fuel > actions_fuel inp [Areg r1] (lk_dir lk).
  Proof.
    intros * FUEL; unfold actions_fuel, actions_fuel_nolk in *; simpl in *.
    pose proof remaining_le_full_length inp (lk_dir lk); destruct first_check_input; nia.
  Qed.

  Lemma quant_free_iter_decreases_fuel:
    forall r inp greedy delta r1 cont dir fuel,
      act_from_regex r inp (Areg (Quantified greedy 0 delta r1) :: cont) dir ->
      S fuel > actions_fuel inp (Areg (Quantified greedy 0 delta r1) :: cont) dir ->
      fuel > actions_fuel inp (Areg r1 :: Acheck inp :: Areg (Quantified greedy 0 (noi_pred delta) r1) :: cont) dir.
  Proof.
    intros r inp greedy delta r1 cont dir fuel AFR FUEL.
    pose proof chunk_size_lt_last r inp _ dir AFR 0 _ eq_refl as LT.
    unfold actions_fuel, actions_fuel_nolk in *.
    cbn [skipn first_check_input chunk_size last_chunk_size actions_fuel'
         actions_lookaround_fuel regex_lookaround_fuel expanded_size] in *.
    rewrite is_strict_suffix_irrefl.
    destruct (first_check_input cont) as [inpchk|];
      [specialize (LT inpchk eq_refl); destruct is_strict_suffix|].
    all: destruct r1 as [| | | |? [|?] ? ?| | | |]; cbn [expanded_size] in *; lia.
  Qed.

  Lemma check_passes_next_check:
    forall r inp inpcheck cont dir inpchknext,
      act_from_regex r inp (Acheck inpcheck :: cont) dir ->
      first_check_input cont = Some inpchknext ->
      is_strict_suffix inp inpcheck dir = true ->
      is_strict_suffix inp inpchknext dir = true.
  Proof.
    intros * AFR%afr_checks_ordered [tl EQ]%actions_checks_first_check_input SS.
    rewrite is_strict_suffix_correct in *; cbn in AFR; rewrite EQ in AFR.
    apply Sorted.Sorted_inv, proj1, Sorted.Sorted_inv, proj2, Sorted.HdRel_inv in AFR as [<-|];
      eauto using strict_suffix_trans.
  Qed.

  Lemma check_decreases_fuel:
    forall r inp inpcheck cont dir fuel,
      act_from_regex r inp (Acheck inpcheck :: cont) dir ->
      is_strict_suffix inp inpcheck dir = true ->
      S fuel > actions_fuel inp (Acheck inpcheck :: cont) dir ->
      fuel > actions_fuel inp cont dir.
  Proof.
    intros r inp inpcheck cont dir fuel AFR SS FUEL.
    destruct (afr_checks_fby_quant _ _ _ _ AFR 0 inpcheck eq_refl) as (greedy & delta & rq & E).
    destruct cont as [|a cont]; [discriminate | injection E as ->].
    unfold actions_fuel, actions_fuel_nolk in *; cbn in *; rewrite SS in FUEL.
    destruct (first_check_input cont) as [inpchknext|] eqn:SNDCHK; cbn in *; [|lia].
    rewrite (check_passes_next_check _ _ _ _ _ _ AFR SNDCHK SS); lia.
  Qed.

  Inductive act_step:
    input -> actions -> Direction -> input -> actions -> Direction -> Prop :=
  | st_epsilon inp cont dir:
      act_step inp (Areg Epsilon :: cont) dir inp cont dir
  | st_char inp cd nextinp cont dir:
      advance_input inp dir = Some nextinp ->
      act_step inp (Areg (Regex.Character cd) :: cont) dir nextinp cont dir
  | st_disj_left inp r1 r2 cont dir:
      act_step inp (Areg (Disjunction r1 r2) :: cont) dir inp (Areg r1 :: cont) dir
  | st_disj_right inp r1 r2 cont dir:
      act_step inp (Areg (Disjunction r1 r2) :: cont) dir inp (Areg r2 :: cont) dir
  | st_sequence inp r1 r2 cont dir:
      act_step inp (Areg (Sequence r1 r2) :: cont) dir inp
        (seq_list r1 r2 dir ++ cont) dir
  | st_quant_forced inp greedy min delta r1 cont dir:
      act_step inp (Areg (Quantified greedy (S min) delta r1) :: cont) dir inp
        (Areg r1 :: Areg (Quantified greedy min delta r1) :: cont) dir
  | st_quant_skip inp greedy delta r1 cont dir:
      act_step inp (Areg (Quantified greedy 0 delta r1) :: cont) dir inp cont dir
  | st_quant_free_iter inp greedy delta delta' r1 cont dir:
      delta = (NoI.N 1 + delta')%NoI ->
      act_step inp (Areg (Quantified greedy 0 delta r1) :: cont) dir inp
        (Areg r1 :: Acheck inp :: Areg (Quantified greedy 0 delta' r1) :: cont) dir
  | st_lk_sub inp lk r1 cont dir:
      act_step inp (Areg (Lookaround lk r1) :: cont) dir inp [Areg r1] (lk_dir lk)
  | st_lk_cont inp lk r1 cont dir:
      act_step inp (Areg (Lookaround lk r1) :: cont) dir inp cont dir
  | st_group inp gid r1 cont dir:
      act_step inp (Areg (Group gid r1) :: cont) dir inp
        (Areg r1 :: Aclose gid :: cont) dir
  | st_anchor inp a cont dir:
      act_step inp (Areg (Anchor a) :: cont) dir inp cont dir
  | st_backref inp gid n nextinp cont dir:
      advance_input_n inp n dir = nextinp ->
      act_step inp (Areg (Backreference gid) :: cont) dir nextinp cont dir
  | st_check inp inpcheck cont dir:
      is_strict_suffix inp inpcheck dir = true ->
      act_step inp (Acheck inpcheck :: cont) dir inp cont dir
  | st_close inp gid cont dir:
      act_step inp (Aclose gid :: cont) dir inp cont dir.

  Lemma act_step_afr r inp act dir inp' act' dir':
    MembershipProof.act_from_regex r inp act dir ->
    act_step inp act dir inp' act' dir' ->
    MembershipProof.act_from_regex r inp' act' dir'.
  Proof.
    intros AFR STEP; destruct STEP; subst; rewrite ?is_strict_suffix_correct in *;
      eauto 2 using MembershipProof.act_from_regex.
    destruct delta as [[|k]|];
      [eapply MembershipProof.afr_pop_quant_done
      |eapply MembershipProof.afr_pop_quant_free_skip with (delta := NoI.N k)
      |eapply MembershipProof.afr_pop_quant_free_skip with (delta := NoI.Inf)]; exact AFR.
  Qed.

  Lemma act_step_nolk inp act dir inp' act' dir':
    act_step inp act dir inp' act' dir' ->
    actions_no_lookaround act -> actions_no_lookaround act'.
  Proof.
    destruct 1; cbn; intuition auto using actions_no_lookaround_seq_list.
  Qed.

  Local Ltac cons_dec a new :=
    apply (cons_decreases_fuel _ a new _ _);
      [exact I | reflexivity | cbn; lia | cbn; lia].

  Lemma act_step_decreases_fuel r inp act dir inp' act' dir':
    MembershipProof.act_from_regex r inp act dir ->
    act_step inp act dir inp' act' dir' ->
    MembershipProof.actions_fuel inp act dir
    > MembershipProof.actions_fuel inp' act' dir'.
  Proof.
    intros AFR STEP; destruct STEP.
    - cons_dec (Areg Epsilon) (@nil action).
    - eauto using MembershipProof.read_decreases_fuel.
    - cons_dec (Areg (Disjunction r1 r2)) [Areg r1].
    - cons_dec (Areg (Disjunction r1 r2)) [Areg r2].
    - destruct dir; [cons_dec (Areg (Sequence r1 r2)) (seq_list r1 r2 forward)
                    | cons_dec (Areg (Sequence r1 r2)) (seq_list r1 r2 backward)].
    - cons_dec (Areg (Quantified greedy (S min) delta r1))
        [Areg r1; Areg (Quantified greedy min delta r1)].
    - cons_dec (Areg (Quantified greedy 0 delta r1)) (@nil action).
    - replace delta' with (noi_pred delta) by (subst; apply MembershipProof.simpl_pred).
      eapply quant_free_iter_decreases_fuel with (r := r); eauto.
    - eapply lk_sub_decreases_fuel with (cont := cont); eauto.
    - cons_dec (Areg (Lookaround lk r1)) (@nil action).
    - cons_dec (Areg (Group gid r1)) [Areg r1; Aclose gid].
    - cons_dec (Areg (Anchor a)) (@nil action).
    - eauto using MembershipProof.read_backref_decreases_fuel.
    - eapply check_decreases_fuel with (r := r); eauto.
    - cons_dec (Aclose gid) (@nil action).
  Qed.

  Corollary act_step_ok r inp act dir inp' act' dir' n:
    MembershipProof.act_from_regex r inp act dir ->
    actions_no_lookaround act ->
    S n > MembershipProof.actions_fuel inp act dir ->
    act_step inp act dir inp' act' dir' ->
    MembershipProof.act_from_regex r inp' act' dir' /\ actions_no_lookaround act'
    /\ n > MembershipProof.actions_fuel inp' act' dir'.
  Proof.
    intros AFR NOLK FUEL STEP; pose proof act_step_decreases_fuel _ _ _ _ _ _ _ AFR STEP.
    repeat split; [eauto using act_step_afr | eauto using act_step_nolk | lia].
  Qed.

  Local Ltac optp_node :=
    repeat match goal with
      | _ => progress cbn [tree_res] in *
      | |- context[greedy_choice ?g _ _] => is_var g; destruct g; cbn [greedy_choice] in *
      | E: read_char _ _ ?i ?d = Some (_, ?ni) |- _ => is_var ni;
          replace ni with (advance_input' i d) in *
            by eauto using advance_input_success, read_char_success_advance
      | E: read_backref _ _ _ ?i ?d = Some (?s, ?ni) |- _ => is_var ni;
          replace ni with (advance_input_n i (length s) d) in *
            by (symmetry; eauto using read_backref_success_advance)
      end.
  Local Ltac optp_unfold :=
    intros; cbn [optp_algo optp_step res_of tree_res];
    repeat match goal with E: ?x = _ |- context[?x] => rewrite E end; reflexivity.
  Local Ltac optp_rec IH st :=
    match goal with
    | AFR: MembershipProof.act_from_regex ?r ?i ?a ?d,
      NOLK: actions_no_lookaround ?a,
      FUEL: S ?n > MembershipProof.actions_fuel ?i ?a ?d |- _ =>
        let A := fresh "AFR" in let N := fresh "NOLK" in let F := fresh "FUEL" in
        destruct (act_step_ok r i a d _ _ _ n AFR NOLK FUEL st) as (A & N & F);
        apply IH with (r := r); assumption
    end.
  Local Ltac optp_go IH st := eapply optp_spec_step; [optp_unfold | optp_rec IH st].
  Local Ltac optp_done := apply optp_spec_done; optp_unfold.

  Theorem optp_max_spec:
    forall act inp gm dir t,
      is_tree rer act inp gm dir t ->
      forall r n,
        MembershipProof.act_from_regex r inp act dir ->
        actions_no_lookaround act ->
        n > MembershipProof.actions_fuel inp act dir ->
        optp_spec n (optp_algo dir (Cfg act inp gm)) (tree_res t gm inp dir).
  Proof.
    induction 1; intros r n AFR NOLK FUEL; destruct n as [|n]; try lia; optp_node.
    - optp_done.
    - apply is_strict_suffix_correct in PROGRESS.
      optp_go IHis_tree (st_check inp strcheck cont dir PROGRESS).
    - apply is_strict_suffix_inv_false in CHECKFAIL; optp_done.
    - optp_go IHis_tree (st_close inp gid cont dir).
    - optp_go IHis_tree (st_epsilon inp cont dir).
    - optp_go IHis_tree (st_char inp cd _ cont dir (read_char_success_advance _ _ _ _ _ _ READ)).
    - optp_done.
    - eapply optp_spec_choice; [optp_unfold | optp_unfold
        | optp_rec IHis_tree1 (st_disj_left inp r1 r2 cont dir)
        | optp_rec IHis_tree2 (st_disj_right inp r1 r2 cont dir)].
    - optp_go IHis_tree (st_sequence inp r1 r2 cont dir).
    - subst gidl; optp_go IHis_tree (st_quant_forced inp greedy min plus r1 cont dir).
    - optp_go IHis_tree (st_quant_skip inp greedy (NoI.N 0) r1 cont dir).
    - subst gidl tquant.
      assert (ITER: optp_spec n (optp_algo dir (Cfg (Areg r1 :: Acheck inp ::
              Areg (Quantified greedy 0 plus r1) :: cont) inp (GroupMap.reset (def_groups r1) gm)))
              (tree_res titer (GroupMap.reset (def_groups r1) gm) inp dir))
        by optp_rec IHis_tree1 (st_quant_free_iter inp greedy
                                  (NoI.N 1 + plus)%NoI plus r1 cont dir eq_refl).
      assert (SKIP': optp_spec n (optp_algo dir (Cfg cont inp gm)) (tree_res tskip gm inp dir))
        by optp_rec IHis_tree2 (st_quant_skip inp greedy (NoI.N 1 + plus)%NoI r1 cont dir).
      rewrite <- (MembershipProof.simpl_pred plus) in ITER.
      destruct plus as [p|]; optp_node;
        (eapply optp_spec_choice; [optp_unfold | optp_unfold | assumption | assumption]).
    - optp_go IHis_tree (st_group inp gid r1 cont dir).
    - destruct NOLK as [[] _].
    - destruct NOLK as [[] _].
    - optp_go IHis_tree (st_anchor inp a cont dir).
    - optp_done.
    - optp_go IHis_tree (st_backref inp gid (length br_str) _ cont dir eq_refl).
    - optp_done.
  Qed.

  Definition optp_run (r: regex) (inp: input): list bool -> match_result :=
    optp_algo forward (Cfg [Areg r] inp GroupMap.empty).

  Definition matched (m: match_result): bool :=
    match m with Success _ => true | _ => false end.

  Definition optp_output (r: regex) (inp: input) (cs: list bool): list bool :=
    matched (optp_run r inp cs) :: cs.

  Lemma optp_output_length r inp cs: length (optp_output r inp cs) = S (length cs).
  Proof. reflexivity. Qed.

  Definition exec_of_parse (r: regex) (inp: input) (bs: list bool): option leaf :=
    match bs with
    | true :: cs => match optp_run r inp cs with Success lf => Some lf | _ => None end
    | _ => None
    end.

  Definition parse_spec (r: regex) (inp: input) (n: nat) (bs: list bool): Prop :=
    (exists cs0, length cs0 = n /\ bs = optp_output r inp cs0) /\
    (forall cs, length cs = n -> bits_le (optp_output r inp cs) bs = true).

  Lemma parse_spec_unique r inp n b1 b2:
      parse_spec r inp n b1 -> parse_spec r inp n b2 -> b1 = b2.
  Proof. intros [[cs1 [L1 ->]] M1] [[cs2 [L2 ->]] M2]; auto using bits_le_antisym. Qed.

  Lemma optp_spec_parse r inp n o:
      optp_spec n (optp_run r inp) o ->
      exists best, parse_spec r inp n best /\ exec_of_parse r inp best = o.
  Proof.
    intros [_ SPEC]; unfold parse_spec, optp_output, matched; destruct o as [lf|].
    - destruct SPEC as (cs0 & LEN0 & SUCC & MAX); exists (true :: cs0); cbn [exec_of_parse].
      rewrite SUCC; repeat apply conj; [exists cs0; now rewrite SUCC | intros cs LEN | reflexivity].
      destruct (optp_run r inp cs) eqn:RES; cbn; try reflexivity; apply MAX; congruence.
    - exists (false :: repeat true n).
      split; [|reflexivity]; split; [exists (repeat true n) | intros cs LEN];
        rewrite SPEC by auto using repeat_length; cbn; auto using repeat_length, bits_le_ones.
  Qed.

  Theorem parse_determines_exec r inp t n best:
      no_lookaround r ->
      is_tree rer [Areg r] inp GroupMap.empty forward t ->
      n > MembershipProof.actions_fuel inp [Areg r] forward ->
      parse_spec r inp n best ->
      exec_of_parse r inp best = tree_res t GroupMap.empty inp forward.
  Proof.
    intros ? ? ? PARSE; edestruct (optp_spec_parse r inp n) as [b [P E]];
      [eapply optp_max_spec with (r := r); cbn; eauto using MembershipProof.afr_refl|].
    now rewrite (parse_spec_unique r inp n best b PARSE P).
  Qed.

  Definition maxb (b1 b2: list bool): list bool := if bits_le b1 b2 then b2 else b1.

  Lemma maxb_le_l b1 b2: bits_le b1 (maxb b1 b2) = true.
  Proof. unfold maxb; destruct (bits_le b1 b2) eqn:B; auto using bits_le_refl. Qed.

  Lemma maxb_le_r b1 b2: bits_le b2 (maxb b1 b2) = true.
  Proof.
    unfold maxb; destruct (bits_le b1 b2) eqn:B; [apply bits_le_refl|].
    destruct (bits_le_total b1 b2); congruence.
  Qed.

  Fixpoint max_out (f: list bool -> list bool) (n: nat): list bool :=
    match n with
    | 0 => f []
    | S n =>
        maxb (max_out (fun cs => f (false :: cs)) n) (max_out (fun cs => f (true :: cs)) n)
    end.

  Lemma max_out_spec n:
    forall f,
      (exists cs, length cs = n /\ max_out f n = f cs) /\
      (forall cs, length cs = n -> bits_le (f cs) (max_out f n) = true).
  Proof.
    induction n as [|n IH]; intro f; cbn [max_out].
    - split; [exists []; auto|]; intros [|b cs] LEN; [apply bits_le_refl | discriminate].
    - destruct (IH (fun cs => f (false :: cs))) as [[cs0 [LEN0 EQ0]] MAX0].
      destruct (IH (fun cs => f (true :: cs))) as [[cs1 [LEN1 EQ1]] MAX1]; split.
      + unfold maxb; destruct bits_le; [exists (true :: cs1) | exists (false :: cs0)]; split; auto; cbn; lia.
      + guess; [eapply bits_le_trans, maxb_le_r | eapply bits_le_trans, maxb_le_l]; eauto.
  Qed.

  Definition parse (r: regex) (inp: input) (n: nat): list bool :=
    max_out (optp_output r inp) n.

  Theorem parse_parse_spec r inp n: parse_spec r inp n (parse r inp n).
  Proof. apply max_out_spec. Qed.

  Theorem optp_membership_exec r inp t n:
      no_lookaround r ->
      is_tree rer [Areg r] inp GroupMap.empty forward t ->
      n > MembershipProof.actions_fuel inp [Areg r] forward ->
      exec_of_parse r inp (parse r inp n) = tree_res t GroupMap.empty inp forward.
  Proof.
    intros; eauto using parse_determines_exec, parse_parse_spec.
  Qed.

  Lemma regex_lookaround_fuel_nolk r:
    forall str, no_lookaround r -> MembershipProof.regex_lookaround_fuel str r = 0.
  Proof. induction r; cbn; intuition (rewrite ?IHr, ?IHr1, ?IHr2; auto). Qed.

  Theorem poly_fuel_nolk inp r:
      no_lookaround r ->
      MembershipProof.actions_fuel inp [Areg r] forward
      = (1 + remaining_length inp forward) * Basics.expanded_size r.
  Proof.
    intro NLK; unfold MembershipProof.actions_fuel, MembershipProof.actions_fuel_nolk; cbn.
    rewrite regex_lookaround_fuel_nolk by assumption; lia.
  Qed.

  Corollary poly_bits inp r:
      no_lookaround r -> no_lower_bound r ->
      S (MembershipProof.actions_fuel inp [Areg r] forward) <= guess_budget r inp.
  Proof.
    intros NLK NLB; unfold guess_budget; rewrite poly_fuel_nolk by assumption.
    pose proof expanded_size_nolb r NLB; nia.
  Qed.

  Corollary optp_membership_poly r inp t:
      no_lookaround r -> no_lower_bound r ->
      is_tree rer [Areg r] inp GroupMap.empty forward t ->
      let n := guess_budget r inp in
      exists best,
        parse_spec r inp n best /\
        length best = S n /\
        exec_of_parse r inp best = tree_res t GroupMap.empty inp forward.
  Proof.
    intros NLK NLB ? n.
    assert (FUEL: n > MembershipProof.actions_fuel inp [Areg r] forward)
      by (pose proof poly_bits inp r NLK NLB; unfold n, guess_budget in *; lia).
    pose proof parse_parse_spec r inp n as PARSE.
    exists (parse r inp n); split; [assumption|]; split.
    - destruct PARSE as [[cs0 [LEN0 ->]] _]; now rewrite optp_output_length, LEN0.
    - now apply optp_membership_exec.
  Qed.

End OptpAlgo.
