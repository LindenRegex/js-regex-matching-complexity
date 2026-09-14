(** * OptP membership for JavaScript regex matching without lookarounds *)

From Linden Require Import Semantics Chars StrictSuffix FunctionalSemantics Tree
  FunctionalUtils ComputeIsTree Semantics.Tree Semantics.Groups.
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

  Local Ltac optp_node :=
    repeat match goal with
      | _ => progress cbn [compute_tree tree_res] in *
      | H: Some _ = Some _ |- _ => injection H as <-
      | |- context[greedy_choice ?g _ _] => is_var g; destruct g; cbn [greedy_choice] in *
      | E: read_char _ _ ?i ?d = Some (_, ?ni) |- _ => is_var ni;
          replace ni with (advance_input' i d) in *
            by eauto using advance_input_success, read_char_success_advance
      | E: read_backref _ _ _ ?i ?d = Some (?s, ?ni) |- _ => is_var ni;
          replace ni with (advance_input_n i (length s) d) in *
            by (symmetry; eauto using read_backref_success_advance)
      | H: context[match ?x with _ => _ end] |- _ => is_var x; destruct x
      | H: context[match ?x with _ => _ end] |- _ => destruct x eqn:?; try discriminate
      end.
  Local Ltac optp_unfold :=
    intros; cbn [optp_algo optp_step res_of tree_res];
    repeat match goal with E: ?x = _ |- context[?x] => rewrite E end; reflexivity.
  Local Ltac optp_nolk := try (cbn [actions_no_lookaround no_lookaround]);
    first [tauto | apply actions_no_lookaround_seq_list; tauto].
  Local Ltac optp_rec R := apply R; [optp_nolk | assumption | lia].
  Local Ltac optp_case R :=
    optp_node;
    first [ apply optp_spec_done; optp_unfold
          | eapply optp_spec_step; [optp_unfold | optp_rec R]
          | eapply optp_spec_choice; [optp_unfold | optp_unfold | optp_rec R | optp_rec R] ].

  Theorem optp_max_spec fuel:
    forall act inp gm dir t,
      actions_no_lookaround act ->
      compute_tree rer act inp gm dir fuel = Some t ->
      forall n, fuel <= n ->
        optp_spec n (optp_algo dir (Cfg act inp gm)) (tree_res t gm inp dir).
  Proof.
    induction fuel as [|fuel IH]; intros act inp gm dir t NOLK COMP [|n] LE;
      try discriminate; try lia.
    destruct act as [|[rg|ic|gidc] cont]; cbn [actions_no_lookaround] in NOLK;
      try match goal with H: _ /\ _ |- _ => destruct H as [NR NC] end;
      try destruct rg as [|cd|r1 r2|r1 r2|greedy [|mn] delta rq|lk rq|gidg rq|anc|gidb];
      try destruct delta as [[|d]|];
      try (cbn [no_lookaround] in NR);
      try contradiction;
      optp_case IH.
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

  Theorem parse_determines_exec r inp fuel t n best:
      no_lookaround r ->
      compute_tree rer [Areg r] inp GroupMap.empty forward fuel = Some t ->
      fuel <= n ->
      parse_spec r inp n best ->
      exec_of_parse r inp best = tree_res t GroupMap.empty inp forward.
  Proof.
    intros ? ? ? PARSE; edestruct (optp_spec_parse r inp n) as [b [P E]];
      [apply optp_max_spec with (fuel := fuel) (t := t); cbn; auto|].
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

  Lemma is_tree_compute: forall r inp t n,
      is_tree rer [Areg r] inp GroupMap.empty forward t ->
      n > MembershipProof.actions_fuel inp [Areg r] forward ->
      compute_tree rer [Areg r] inp GroupMap.empty forward n = Some t.
  Proof.
    intros r inp t n TREE FUEL.
    pose proof MembershipProof.functional_terminates' r inp [Areg r] forward
      (MembershipProof.afr_refl r inp) n FUEL
      GroupMap.empty rer.
    destruct compute_tree as [t'|] eqn:COMPUTE; [|congruence].
    f_equal; eauto using compute_is_tree, is_tree_determ.
  Qed.

  Theorem optp_membership_exec r inp t n:
      no_lookaround r ->
      is_tree rer [Areg r] inp GroupMap.empty forward t ->
      n > MembershipProof.actions_fuel inp [Areg r] forward ->
      exec_of_parse r inp (parse r inp n) = tree_res t GroupMap.empty inp forward.
  Proof.
    intros; eapply parse_determines_exec with (fuel := n) (t := t);
      eauto using is_tree_compute, parse_parse_spec.
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
