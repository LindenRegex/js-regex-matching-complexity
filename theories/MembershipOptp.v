(** * OptP membership for JavaScript regex matching without lookarounds *)

From Linden Require Import Semantics Chars StrictSuffix FunctionalSemantics Tree
  Semantics.Tree Semantics.Groups.
From Warblre Require Import Base spec.RegExpRecord.
From Stdlib Require Import List Lia.
Import ListNotations.
From JSRegexComplexity Require Import MembershipProof Bits.
From JSRegexComplexity Require Export Basics.

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

  (* Let `res` be a function from lists of booleans to match results.
  `optp_spec n res o` is true when:
  - `res` never runs out of fuel on inputs of length `n`,
  - if `o` is `None`, then all branches of `res` fail to find a match,
  - if `o` is `Some lf`, then there is a branch of `res` that yields `lf` and is the lexicographically highest branch that yields a result.
  Essentially, `o` must be the OptP result of `res`. *)
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

  (* Utility lemma for disjunctions: if `res` branches between `res1` and `res2`,
  then for all results `o1` and `o2`, if `o1` is the result of `res1` and `o2` is
  the result of `res2`, then `seqop o1 o2` is the result of `res`. *)
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

  (* Utility lemma for no branching case. *)
  Lemma optp_spec_step n res res' o:
      (forall b cs, res (b :: cs) = res' cs) -> optp_spec n res' o -> optp_spec (S n) res o.
  Proof.
    intros; replace o with (seqop o o) by (now destruct o); eauto using optp_spec_choice.
  Qed.

  Definition res_of (o: option leaf): match_result :=
    match o with Some lf => Success lf | None => NoMatch end.

  (* Utility lemma for constant results. *)
  Lemma optp_spec_const n o: optp_spec n (fun _ => res_of o) o.
  Proof.
    destruct o as [lf|]; split; intros; try discriminate; try reflexivity;
      exists (repeat true n); auto using repeat_length, bits_le_ones.
  Qed.

  (* Utility lemma for results that are constant for nonempty bitstrings. *)
  Lemma optp_spec_done n res o:
      (forall b cs, res (b :: cs) = res_of o) -> optp_spec (S n) res o.
  Proof.
    intros; apply optp_spec_step with (res' := fun _ => res_of o); auto using optp_spec_const.
  Qed.

  Lemma act_step_nolk dir act inp act' inp':
    MembershipProof.act_step dir act inp act' inp' ->
    actions_no_lookaround act -> actions_no_lookaround act'.
  Proof.
    destruct 1; cbn; intuition auto using actions_no_lookaround_seq_list.
  Qed.

  Corollary act_step_ok r dir act inp act' inp' n:
    MembershipProof.act_from_regex r dir act ->
    actions_no_lookaround act ->
    S n > MembershipProof.actions_fuel r inp act dir ->
    MembershipProof.act_step dir act inp act' inp' ->
    MembershipProof.act_from_regex r dir act' /\ actions_no_lookaround act'
    /\ n > MembershipProof.actions_fuel r inp' act' dir.
  Proof.
    intros AFR NOLK FUEL STEP; pose proof MembershipProof.fuel_decreases AFR STEP.
    repeat split; eauto using MembershipProof.afr_step, act_step_nolk; lia.
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
      | H: strict_suffix _ _ _ |- _ => apply is_strict_suffix_correct in H
      | H: ~ strict_suffix _ _ _ |- _ => apply is_strict_suffix_inv_false in H
      end.
  Local Ltac optp_unfold :=
    intros; cbn [optp_algo optp_step res_of tree_res];
    repeat match goal with E: ?x = _ |- context[?x] => rewrite E end; reflexivity.
  Local Ltac optp_rec :=
    match goal with
    | AFR: MembershipProof.act_from_regex ?r ?d ?a,
      NOLK: actions_no_lookaround ?a,
      FUEL: S ?n > MembershipProof.actions_fuel ?r ?i ?a ?d,
      IH: forall r n, _ -> _ -> _ -> optp_spec n (optp_algo ?d (Cfg ?a' ?i' _)) _ |- _ =>
        assert (STEP: MembershipProof.act_step d a i a' i')
          by eauto using MembershipProof.act_step, read_suffix, read_char_success_advance;
        destruct (act_step_ok r d a i a' i' n AFR NOLK FUEL STEP) as (? & ? & ?);
        apply IH with (r := r); assumption
    end.
  Local Ltac optp_go := eapply optp_spec_step; [optp_unfold | optp_rec].
  Local Ltac optp_branch :=
    eapply optp_spec_choice; [optp_unfold | optp_unfold | optp_rec | optp_rec].

  (* Main theorem: *)
  Theorem optp_max_spec:
    (* for any semantic state (act, inp, gm, dir) and its associated backtracking tree t, *)
    forall act inp gm dir t,
      is_tree rer act inp gm dir t ->
      (* if this semantic state comes from a regex and does not contain lookarounds,*)
      forall r n,
        MembershipProof.act_from_regex r dir act ->
        actions_no_lookaround act ->
        (* then for any n greater than the fuel of (inp, act, dir), *)
        n > MembershipProof.actions_fuel r inp act dir ->
        (* the result of optp_algo with the semantic state over bitstrings of length n
        is the same as the first leaf of t. *)
        optp_spec n (optp_algo dir (Cfg act inp gm)) (tree_res t gm inp dir).
  Proof.
    induction 1; intros r n AFR NOLK FUEL; destruct n as [|n]; try lia; optp_node; subst.
    all: try solve [apply optp_spec_done; optp_unfold | optp_go
                   | destruct NOLK as [[] _]].
    - optp_branch.
    - rewrite <- (MembershipProof.simpl_pred plus) in IHis_tree1.
      destruct plus; optp_node; optp_branch.
    - destruct (advance_input_n_suffix inp (length br_str) dir _ eq_refl) as [EQ|?];
        [rewrite EQ in *|]; optp_go.
  Qed.

  (* Specialization of optp_algo to a regex and an input. *)
  Definition optp_run (r: regex) (inp: input): list bool -> match_result :=
    optp_algo forward (Cfg [Areg r] inp GroupMap.empty).

  (* The result bit to prepend to the list of choices. *)
  Definition matched (m: match_result): bool :=
    match m with Success _ => true | _ => false end.

  (* Prepending the result bit to the result of optp_run gives the OptP output. *)
  Definition optp_output (r: regex) (inp: input) (cs: list bool): list bool :=
    matched (optp_run r inp cs) :: cs.

  Lemma optp_output_length r inp cs: length (optp_output r inp cs) = S (length cs).
  Proof. reflexivity. Qed.

  (* Retrieving the matching result from the parsing result; this can be done by running `optp_run` on the parsing result minus the first bit. *)
  Definition exec_of_parse (r: regex) (inp: input) (bs: list bool): option leaf :=
    match bs with
    | true :: cs => match optp_run r inp cs with Success lf => Some lf | _ => None end
    | _ => None
    end.

  (* `parse_spec r inp n bs` is true when `bs` is the maximum output of `optp_output r inp` on bitstrings of length `n`. *)
  Definition parse_spec (r: regex) (inp: input) (n: nat) (bs: list bool): Prop :=
    (exists cs0, length cs0 = n /\ bs = optp_output r inp cs0) /\
    (forall cs, length cs = n -> bits_le (optp_output r inp cs) bs = true).

  Lemma parse_spec_unique r inp n b1 b2:
      parse_spec r inp n b1 -> parse_spec r inp n b2 -> b1 = b2.
  Proof. intros [[cs1 [L1 ->]] M1] [[cs2 [L2 ->]] M2]; auto using bits_le_antisym. Qed.

  (* Let `n` ∈ ℕ, `r` a regex, `inp` an input.
  If `o` is the maximum output of `optp_run`, then `o` can be retrieved from the bits output by the OptP algorithm. *)
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

  (* The result of parsing determines the result of execution. *)
  Theorem parse_determines_exec r inp t n best:
      no_lookaround r ->
      is_tree rer [Areg r] inp GroupMap.empty forward t ->
      n > MembershipProof.actions_fuel r inp [Areg r] forward ->
      parse_spec r inp n best ->
      exec_of_parse r inp best = tree_res t GroupMap.empty inp forward.
  Proof.
    intros ? ? ? PARSE; edestruct (optp_spec_parse r inp n) as [b [P E]];
      [eapply optp_max_spec with (r := r); cbn; eauto using MembershipProof.afr_refl|].
    now rewrite (parse_spec_unique r inp n best b PARSE P).
  Qed.

  (* The maximum between b1 and b2 in lexicographic order. *)
  Definition maxb (b1 b2: list bool): list bool := if bits_le b1 b2 then b2 else b1.

  Lemma maxb_le_l b1 b2: bits_le b1 (maxb b1 b2) = true.
  Proof. unfold maxb; destruct (bits_le b1 b2) eqn:B; auto using bits_le_refl. Qed.

  Lemma maxb_le_r b1 b2: bits_le b2 (maxb b1 b2) = true.
  Proof.
    unfold maxb; destruct (bits_le b1 b2) eqn:B; [apply bits_le_refl|].
    destruct (bits_le_total b1 b2); congruence.
  Qed.

  (* A function to naively compute the maximum output of a function f on inputs of length n. *)
  Fixpoint max_out (f: list bool -> list bool) (n: nat): list bool :=
    match n with
    | 0 => f []
    | S n =>
        maxb (max_out (fun cs => f (false :: cs)) n) (max_out (fun cs => f (true :: cs)) n)
    end.

  (* `max_out f n` indeed returns the maximum output of function `f` on inputs of length `n`. *)
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

  (* A function that computes the result of the OptP algorithm on inputs of length `n`. *)
  Definition parse (r: regex) (inp: input) (n: nat): list bool :=
    max_out (optp_output r inp) n.

  Theorem parse_parse_spec r inp n: parse_spec r inp n (parse r inp n).
  Proof. apply max_out_spec. Qed.

  Theorem optp_membership_exec r inp t n:
      no_lookaround r ->
      is_tree rer [Areg r] inp GroupMap.empty forward t ->
      n > MembershipProof.actions_fuel r inp [Areg r] forward ->
      exec_of_parse r inp (parse r inp n) = tree_res t GroupMap.empty inp forward.
  Proof.
    intros; eauto using parse_determines_exec, parse_parse_spec.
  Qed.

  Lemma regex_lookaround_fuel_nolk r:
    forall str, no_lookaround r -> MembershipProof.regex_lookaround_fuel str r = 0.
  Proof. induction r; cbn; intuition (rewrite ?IHr, ?IHr1, ?IHr2; auto). Qed.

  Lemma core_size_nolk r:
      no_lookaround r -> MembershipProof.core_size r = Basics.expanded_size r.
  Proof. unfold MembershipProof.core_size; induction r; cbn; intuition nia. Qed.

  Theorem poly_fuel_nolk inp r:
      no_lookaround r ->
      MembershipProof.actions_fuel r inp [Areg r] forward
      = MembershipProof.iter_size r * remaining_length inp forward
        + Basics.expanded_size r.
  Proof.
    intro NLK; rewrite MembershipProof.actions_fuel_init,
      regex_lookaround_fuel_nolk, core_size_nolk by assumption; lia.
  Qed.

  Corollary poly_bits inp r:
      no_lookaround r ->
      S (MembershipProof.actions_fuel r inp [Areg r] forward) <= guess_budget r inp.
  Proof.
    intro NLK; unfold guess_budget; rewrite poly_fuel_nolk by assumption.
    pose proof core_size_nolk r NLK; pose proof MembershipProof.skip_size_pos r.
    unfold MembershipProof.core_size in *; nia.
  Qed.

  Theorem optp_membership_fuel r inp t n:
      no_lookaround r ->
      is_tree rer [Areg r] inp GroupMap.empty forward t ->
      n > MembershipProof.actions_fuel r inp [Areg r] forward ->
      exists best,
        parse_spec r inp n best /\
        length best = S n /\
        exec_of_parse r inp best = tree_res t GroupMap.empty inp forward.
  Proof.
    intros NLK TREE FUEL; pose proof parse_parse_spec r inp n as PARSE.
    exists (parse r inp n); split; [exact PARSE|]; split; [|now apply optp_membership_exec].
    destruct PARSE as [[cs0 [LEN0 ->]] _]; now rewrite optp_output_length, LEN0.
  Qed.

  Corollary optp_membership_poly r inp t:
      no_lookaround r ->
      is_tree rer [Areg r] inp GroupMap.empty forward t ->
      let n := guess_budget r inp in
      exists best,
        parse_spec r inp n best /\
        length best = S n /\
        exec_of_parse r inp best = tree_res t GroupMap.empty inp forward.
  Proof.
    intros NLK TREE n; unfold n; eauto using optp_membership_fuel, poly_bits.
  Qed.

End OptpAlgo.
