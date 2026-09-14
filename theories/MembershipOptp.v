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
        | SBranch hi lo => optp_algo dir (if b then lo else hi) cs
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
                 forall cs, length cs = n -> res cs <> NoMatch -> bits_le cs0 cs = true
    end.

  Local Ltac guess :=
    intros [|[] cs] LEN; cbn in LEN; try discriminate; injection LEN as LEN.

  Lemma optp_spec_choice n res res1 res2 o1 o2:
      (forall cs, res (false :: cs) = res1 cs) ->
      (forall cs, res (true :: cs) = res2 cs) ->
      optp_spec n res1 o1 -> optp_spec n res2 o2 ->
      optp_spec (S n) res (seqop o1 o2).
  Proof.
    intros EL ER [NOF1 S1] [NOF2 S2].
    assert (NOF: forall cs, length cs = S n -> res cs <> Out_of_fuel)
      by (guess; [rewrite ER; apply NOF2 | rewrite EL; apply NOF1]; assumption).
    destruct o1 as [lf1|]; cbn [seqop]; split; try assumption.
    - destruct S1 as [cs0 [LEN0 [SUCC MIN]]].
      exists (false :: cs0); split; [cbn; lia|]; split; [now rewrite EL|].
      guess; intros NM; cbn; [reflexivity | apply MIN; [assumption|]; now rewrite EL in NM].
    - destruct o2 as [lf2|].
      + destruct S2 as [cs0 [LEN0 [SUCC MIN]]].
        exists (true :: cs0); split; [cbn; lia|]; split; [now rewrite ER|].
        guess; intros NM; cbn; [apply MIN; [assumption|]; now rewrite ER in NM
                              | exfalso; rewrite EL in NM; apply NM, S1; assumption].
      + guess; [rewrite ER; apply S2 | rewrite EL; apply S1]; assumption.
  Qed.

  Lemma optp_spec_step n res res' o:
      (forall b cs, res (b :: cs) = res' cs) -> optp_spec n res' o -> optp_spec (S n) res o.
  Proof.
    intros; replace o with (seqop o o) by now destruct o.
    apply optp_spec_choice with (res1 := res') (res2 := res'); auto.
  Qed.

  Definition res_of (o: option leaf): match_result :=
    match o with Some lf => Success lf | None => NoMatch end.

  Lemma optp_spec_const n o: optp_spec n (fun _ => res_of o) o.
  Proof.
    destruct o as [lf|]; split; intros; try discriminate; auto.
    exists (repeat false n); rewrite repeat_length; auto using bits_le_zeros.
  Qed.

  Lemma optp_spec_done n res o:
      (forall b cs, res (b :: cs) = res_of o) -> optp_spec (S n) res o.
  Proof.
    intro EQ; apply optp_spec_step with (res' := fun _ => res_of o);
      auto using optp_spec_const.
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

  Theorem optp_min_spec fuel:
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

  Definition no_match (m: match_result): bool :=
    match m with Success _ => false | _ => true end.

  Definition optp_output (r: regex) (inp: input) (cs: list bool): list bool :=
    no_match (optp_run r inp cs) :: cs.

  Lemma optp_output_length r inp cs: length (optp_output r inp cs) = S (length cs).
  Proof. reflexivity. Qed.

  Definition exec_of_parse (r: regex) (inp: input) (bs: list bool): option leaf :=
    match bs with
    | false :: cs => match optp_run r inp cs with Success lf => Some lf | _ => None end
    | _ => None
    end.

  Definition parse_spec (r: regex) (inp: input) (n: nat) (bs: list bool): Prop :=
    (exists cs0, length cs0 = n /\ bs = optp_output r inp cs0) /\
    (forall cs, length cs = n -> bits_le bs (optp_output r inp cs) = true).

  Lemma parse_spec_unique r inp n b1 b2:
      parse_spec r inp n b1 -> parse_spec r inp n b2 -> b1 = b2.
  Proof. intros [[cs1 [L1 ->]] M1] [[cs2 [L2 ->]] M2]; apply bits_le_antisym; auto. Qed.

  Lemma optp_spec_parse r inp n o:
      optp_spec n (optp_run r inp) o ->
      exists best, parse_spec r inp n best /\ exec_of_parse r inp best = o.
  Proof.
    intros [_ SPEC]; unfold parse_spec, optp_output, no_match.
    destruct o as [lf|].
    - destruct SPEC as [cs0 [LEN0 [SUCC MIN]]]; exists (false :: cs0).
      split; [|cbn [exec_of_parse]; now rewrite SUCC]; split; [exists cs0; now rewrite SUCC|].
      intros cs LEN; destruct (optp_run r inp cs) eqn:RES; cbn;
        [reflexivity | reflexivity | apply MIN; [assumption | congruence]].
    - exists (true :: repeat false n).
      split; [|reflexivity]; split; [exists (repeat false n) | intros cs LEN].
      + rewrite (SPEC _ (repeat_length _ _)); split; [apply repeat_length | reflexivity].
      + rewrite (SPEC cs LEN); cbn; now apply bits_le_zeros.
  Qed.

  Theorem parse_determines_exec r inp fuel t n best:
      no_lookaround r ->
      compute_tree rer [Areg r] inp GroupMap.empty forward fuel = Some t ->
      fuel <= n ->
      parse_spec r inp n best ->
      exec_of_parse r inp best = tree_res t GroupMap.empty inp forward.
  Proof.
    intros ? ? ? PARSE.
    destruct (optp_spec_parse r inp n (tree_res t GroupMap.empty inp forward))
      as [b [P E]]; [apply optp_min_spec with (fuel := fuel) (t := t); cbn; auto|].
    now rewrite (parse_spec_unique r inp n best b PARSE P).
  Qed.

  Definition minb (b1 b2: list bool): list bool := if bits_le b1 b2 then b1 else b2.

  Lemma minb_le_l b1 b2: bits_le (minb b1 b2) b1 = true.
  Proof.
    unfold minb; destruct (bits_le b1 b2) eqn:B; [apply bits_le_refl|].
    destruct (bits_le_total b1 b2); congruence.
  Qed.

  Lemma minb_le_r b1 b2: bits_le (minb b1 b2) b2 = true.
  Proof. unfold minb; destruct (bits_le b1 b2) eqn:B; auto using bits_le_refl. Qed.

  Fixpoint min_out (f: list bool -> list bool) (n: nat): list bool :=
    match n with
    | 0 => f []
    | S n =>
        minb (min_out (fun cs => f (false :: cs)) n) (min_out (fun cs => f (true :: cs)) n)
    end.

  Lemma min_out_spec n:
    forall f,
      (exists cs, length cs = n /\ min_out f n = f cs) /\
      (forall cs, length cs = n -> bits_le (min_out f n) (f cs) = true).
  Proof.
    induction n as [|n IH]; intro f; cbn [min_out].
    - split; [exists []; auto|]; intros [|b cs]; [intros _; apply bits_le_refl | discriminate].
    - destruct (IH (fun cs => f (false :: cs))) as [[cs0 [LEN0 EQ0]] MIN0].
      destruct (IH (fun cs => f (true :: cs))) as [[cs1 [LEN1 EQ1]] MIN1]; split.
      + unfold minb; destruct bits_le; [exists (false :: cs0) | exists (true :: cs1)];
          (split; [cbn; lia | assumption]).
      + guess; [eapply bits_le_trans; [apply minb_le_r | now apply MIN1]
               | eapply bits_le_trans; [apply minb_le_l | now apply MIN0]].
  Qed.

  Definition parse (r: regex) (inp: input) (n: nat): list bool :=
    min_out (optp_output r inp) n.

  Theorem parse_parse_spec r inp n: parse_spec r inp n (parse r inp n).
  Proof. apply min_out_spec. Qed.

  Lemma is_tree_compute: forall r inp t n,
      is_tree rer [Areg r] inp GroupMap.empty forward t ->
      n > MembershipProof.actions_fuel inp [Areg r] forward ->
      compute_tree rer [Areg r] inp GroupMap.empty forward n = Some t.
  Proof.
    intros r inp t n TREE FUEL.
    pose proof MembershipProof.functional_terminates' r inp [Areg r] forward
      (MembershipProof.supported_regex_all r) (MembershipProof.afr_refl r inp) n FUEL
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
    intros; apply parse_determines_exec with (fuel := n) (t := t) (n := n);
      auto using is_tree_compute, parse_parse_spec.
  Qed.

  Lemma regex_lookaround_fuel_nolk r:
    forall str, no_lookaround r -> MembershipProof.regex_lookaround_fuel str r = 0.
  Proof. induction r; cbn; intuition (rewrite ?IHr, ?IHr1, ?IHr2; auto). Qed.

  Theorem poly_fuel_nolk inp r:
      no_lookaround r ->
      MembershipProof.actions_fuel inp [Areg r] forward
      = (1 + remaining_length inp forward) * Basics.expanded_size r.
  Proof.
    intro NLK.
    unfold MembershipProof.actions_fuel, MembershipProof.actions_fuel_nolk.
    simpl MembershipProof.first_check_input. cbv match.
    simpl MembershipProof.chunk_size. simpl MembershipProof.actions_lookaround_fuel.
    rewrite regex_lookaround_fuel_nolk by assumption.
    rewrite PeanoNat.Nat.add_0_r. lia.
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
