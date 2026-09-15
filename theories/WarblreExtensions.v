From Warblre Require Import Patterns Numeric Node NodeProps StaticSemantics Result
  Base EarlyErrors Parameters RegExpRecord Semantics Frontend Notation Errors Typeclasses Match.
From Stdlib Require Import List Lia PeanoNat ZArith.
Import ListNotations.

Section WarblreEarlyErrors.
  Context {params: Parameters}.

  Definition quantprefix_min (p: Patterns.QuantifierPrefix): nat :=
    match p with
    | Patterns.Star | Patterns.Question => 0
    | Patterns.Plus => 1
    | Patterns.RepExact n | Patterns.RepPartialRange n | Patterns.RepRange n _ => n
    end.

  Definition quantifier_min (q: Patterns.Quantifier): nat :=
    match q with Patterns.Greedy p | Patterns.Lazy p => quantprefix_min p end.

  Fixpoint pattern_expanded_size (r: Patterns.Regex): nat :=
    match r with
    | Patterns.Disjunction r1 r2 | Patterns.Seq r1 r2 =>
        1 + pattern_expanded_size r1 + pattern_expanded_size r2
    | Patterns.Quantified r1 q => (1 + quantifier_min q) * (3 + pattern_expanded_size r1)
    | Patterns.Group _ r1 => 2 + pattern_expanded_size r1
    | Patterns.Lookahead r1 | Patterns.NegativeLookahead r1
    | Patterns.Lookbehind r1 | Patterns.NegativeLookbehind r1 => 1 + pattern_expanded_size r1
    | _ => 1
    end.

  Lemma pattern_expanded_size_pos r: 1 <= pattern_expanded_size r.
  Proof. destruct r; cbn; nia. Qed.

  Fixpoint pattern_no_lookaround (r: Patterns.Regex): Prop :=
    match r with
    | Patterns.Disjunction r1 r2 | Patterns.Seq r1 r2 =>
        pattern_no_lookaround r1 /\ pattern_no_lookaround r2
    | Patterns.Quantified r1 _ | Patterns.Group _ r1 => pattern_no_lookaround r1
    | Patterns.Lookahead _ | Patterns.NegativeLookahead _
    | Patterns.Lookbehind _ | Patterns.NegativeLookbehind _ => False
    | _ => True
    end.

  Fixpoint pattern_no_neg_lookaround (r: Patterns.Regex): Prop :=
    match r with
    | Patterns.Disjunction r1 r2 | Patterns.Seq r1 r2 =>
        pattern_no_neg_lookaround r1 /\ pattern_no_neg_lookaround r2
    | Patterns.Quantified r1 _ | Patterns.Group _ r1
    | Patterns.Lookahead r1 | Patterns.Lookbehind r1 => pattern_no_neg_lookaround r1
    | Patterns.NegativeLookahead _ | Patterns.NegativeLookbehind _ => False
    | _ => True
    end.

  Definition quantprefix_no_lower_bound (p: Patterns.QuantifierPrefix): Prop :=
    match p with
    | Patterns.Star | Patterns.Question => True
    | Patterns.Plus => False
    | Patterns.RepExact n | Patterns.RepPartialRange n | Patterns.RepRange n _ => n = 0
    end.

  Definition quantifier_no_lower_bound (q: Patterns.Quantifier): Prop :=
    match q with Patterns.Greedy p | Patterns.Lazy p => quantprefix_no_lower_bound p end.

  Fixpoint pattern_no_lower_bound (r: Patterns.Regex): Prop :=
    match r with
    | Patterns.Disjunction r1 r2 | Patterns.Seq r1 r2 =>
        pattern_no_lower_bound r1 /\ pattern_no_lower_bound r2
    | Patterns.Quantified r1 q => quantifier_no_lower_bound q /\ pattern_no_lower_bound r1
    | Patterns.Group _ r1 | Patterns.Lookahead r1 | Patterns.NegativeLookahead r1
    | Patterns.Lookbehind r1 | Patterns.NegativeLookbehind r1 => pattern_no_lower_bound r1
    | _ => True
    end.

  Definition simple_quantifier (q: Patterns.Quantifier): Prop :=
    match q with
    | Patterns.Greedy p | Patterns.Lazy p =>
        match p with Patterns.RepRange lo hi => lo <= hi | _ => True end
    end.

  Fixpoint simple_regex (n: nat) (r: Patterns.Regex): Prop :=
    match r with
    | Patterns.Empty | Patterns.Char _ | Patterns.Dot
    | Patterns.InputStart | Patterns.InputEnd
    | Patterns.WordBoundary | Patterns.NotWordBoundary => True
    | Patterns.AtomEsc (Patterns.DecimalEsc k) => positive_to_nat k <= n
    | Patterns.AtomEsc (Patterns.GroupEsc _) => False
    | Patterns.AtomEsc _ => True
    | Patterns.CharacterClass _ => False
    | Patterns.Disjunction r1 r2 | Patterns.Seq r1 r2 =>
        simple_regex n r1 /\ simple_regex n r2
    | Patterns.Quantified r1 q => simple_regex n r1 /\ simple_quantifier q
    | Patterns.Group None r1 => simple_regex n r1
    | Patterns.Group (Some _) _ => False
    | Patterns.Lookahead r1 | Patterns.NegativeLookahead r1
    | Patterns.Lookbehind r1 | Patterns.NegativeLookbehind r1 => simple_regex n r1
    end.

  Lemma simple_Pass_Quantifier q: simple_quantifier q -> EarlyErrors.Pass_Quantifier q.
  Proof. destruct q as [[]|[]]; constructor; now constructor. Qed.

  Local Ltac peel_simple :=
    repeat match goal with
           | [ H: simple_regex _ _ |- _ ] => progress cbn [simple_regex] in H
           | [ H: simple_quantifier _ |- _ ] => apply simple_Pass_Quantifier in H
           | [ H: List.In _ nil |- _ ] => destruct H
           | [ H: List.In _ (_ ++ _) |- _ ] => apply in_app_or in H; destruct H
           | [ H: _ /\ _ |- _ ] => destruct H
           | [ H: False |- _ ] => destruct H
           | [ x: option Patterns.GroupName |- _ ] => destruct x
           | [ x: Patterns.AtomEscape |- _ ] => destruct x
           end.

  Lemma simple_regex_walk r:
    forall n ctx nd,
      simple_regex n r ->
      List.In nd (Zipper.Walk.walk r ctx) ->
      simple_regex n (fst nd).
  Proof.
    induction r; intros n ctx nd SIMPLE IN; cbn [Zipper.Walk.walk] in IN;
      destruct IN as [<- | IN]; try exact SIMPLE; peel_simple; eauto.
  Qed.

  Lemma simple_Pass_Regex r:
    forall ctx,
      simple_regex (StaticSemantics.countLeftCapturingParensWithin (Node.zip r ctx) nil) r ->
      EarlyErrors.Pass_Regex r ctx.
  Proof.
    induction r; intros ctx SIMPLE; peel_simple; constructor; auto; now constructor.
  Qed.

  Theorem simple_earlyErrors r:
      simple_regex (StaticSemantics.countLeftCapturingParensWithin r nil) r ->
      StaticSemantics.earlyErrors r nil = Success false.
  Proof.
    intro SIMPLE; unfold StaticSemantics.earlyErrors.
    erewrite EarlyErrors.exist_all_false; [now apply EarlyErrors.soundness_rec, simple_Pass_Regex|].
    intros [r0 ctx0] IN0. apply EarlyErrors.exist_all_false. intros [] _.
    destruct (_ =?= _)%wt, r0; try reflexivity.
    destruct name; [|reflexivity]. exfalso; exact (simple_regex_walk _ _ _ _ SIMPLE IN0).
  Qed.

End WarblreEarlyErrors.

Section CharPos.
  Context {params: Parameters}.

  (* Where the [i]th character of [String.to_char_list s] starts in [s]. *)
  Fixpoint char_pos (s: Parameters.String) (i: nat): nat :=
    match i with
    | 0 => 0
    | S i => String.advanceStringIndex s (char_pos s i)
    end.
End CharPos.

Definition defined_bits {A} (l: list (option A)): list bool :=
  List.map (fun o => match o with Some _ => true | None => false end) l.

Definition capture_substring {params: Parameters} (S: Parameters.String)
    (c: option Notation.CaptureRange): option Parameters.String :=
  match c with
  | None => None
  | Some cr =>
      Some (String.substring S
              (String.getStringIndex S (Z.to_nat (Notation.CaptureRange.startIndex cr)))
              (String.getStringIndex S (Z.to_nat (Notation.CaptureRange.endIndex cr))))
  end.

Definition capture_record {params: Parameters} (S: Parameters.String)
    (c: option Notation.CaptureRange): option MatchRecord :=
  match c with
  | None => None
  | Some cr =>
      Some (MatchRecord.mk
              (String.getStringIndex S (Z.to_nat (Notation.CaptureRange.startIndex cr)))
              (String.getStringIndex S (Z.to_nat (Notation.CaptureRange.endIndex cr))))
  end.

Definition match_substring {params: Parameters}
    (S: Parameters.String) (ms: Notation.MatchState): Parameters.String :=
  String.substring S 0
    (String.getStringIndex S (Z.to_nat (Notation.MatchState.endIndex ms))).

Definition exec_agrees {params: Parameters}
    (R: RegExpInstance) (S: Parameters.String) (res: option Notation.MatchState): Prop :=
  match regExpExec R S, res with
  | Success (Null _), None => True
  | Success (Exotic A _), Some ms =>
      ExecArrayExotic.index A = 0 /\
      ExecArrayExotic.input A = S /\
      ExecArrayExotic.array A
      = Some (match_substring S ms)
        :: List.map (capture_substring S) (Notation.MatchState.captures ms)
  | _, _ => False
  end.

Lemma defined_bits_captures {params: Parameters} (S: Parameters.String) cs:
    defined_bits (List.map (capture_substring S) cs) = defined_bits cs.
Proof. unfold defined_bits; rewrite map_map; apply map_ext; now intros []. Qed.

(* Laws on the string operations of [Parameters] needed by [regExpBuiltinExec] *)
Class StringLaws {params: Parameters}: Prop := {
  advanceStringIndex_progress: forall s i, i < String.advanceStringIndex s i;
  advanceStringIndex_end: forall s, char_pos s (length (String.to_char_list s)) = String.length s;
  getStringIndex_char_pos:
    forall s i, i <= length (String.to_char_list s) -> String.getStringIndex s i = char_pos s i;
}.

Definition rer_of {params: Parameters} (wr: Patterns.Regex) (flags: RegExpFlags): RegExpRecord :=
  reg_exp_record (RegExpFlags.i flags) (RegExpFlags.m flags) (RegExpFlags.s flags)
    (RegExpFlags.u flags) (StaticSemantics.countLeftCapturingParensWithin wr []).

(* 22.2.3.3 steps 17-19 *)
Lemma regExpInitialize_record {params: Parameters} wr flags inst:
    Frontend.regExpInitialize wr flags = Success inst ->
    RegExpInstance.regExpRecord inst = rer_of wr flags.
Proof.
  unfold Frontend.regExpInitialize; destruct (Semantics.compilePattern _ _); [|discriminate].
  now intros [= <-].
Qed.

Lemma rer_of_complete {params: Parameters} wr rer:
    RegExpRecord.capturingGroupsCount rer
    = StaticSemantics.countLeftCapturingParensWithin wr [] ->
    exists flags, rer = rer_of wr flags.
Proof.
  destruct rer as [ic ml da [] n]; cbn; intros ->;
    exists (reg_exp_flags false false ic ml da tt false); reflexivity.
Qed.

Lemma reg_exp_flags_complete (i: bool) (flags: RegExpFlags):
    RegExpFlags.d flags = false ->
    RegExpFlags.i flags = i ->
    RegExpFlags.y flags = true ->
    exists g m s, flags = reg_exp_flags false g i m s tt true.
Proof.
  destruct flags as [d g ic m s [] y]; cbn; intros -> -> ->; now exists g, m, s.
Qed.

Section ExecSucceeds.
  Context {params: Parameters}.

  Notation isGroup := (fun n => match n with (Patterns.Group _ _, _) => true | _ => false end).

  Lemma walk_group_count (r: Patterns.Regex): forall ctx,
      length (List.filter isGroup (Zipper.Walk.walk r ctx))
      = StaticSemantics.countLeftCapturingParensWithin_impl r.
  Proof. induction r; intro; cbn; rewrite ?filter_app, ?length_app; cbn; auto. Qed.

  Lemma nth_group_ok (r: Patterns.Regex) i:
      1 <= i <= StaticSemantics.countLeftCapturingParensWithin_impl r ->
      exists gn r' ctx,
        (StaticSemantics.nth_group r i: Result.Result _ MatchError)
        = Success (Patterns.Group gn r', ctx).
  Proof.
    intros []; assert (BOUND: (i - 1 < length (List.filter isGroup (Zipper.Walk.walk r [])))%nat)
      by (rewrite walk_group_count; lia).
    destruct (proj2 (@Warblre.utils.List.List.Indexing.Nat.success_bounds0 _ MatchError _ _ (i - 1)) BOUND)
      as [[n c] E].
    assert (IN: In (n, c) (List.filter isGroup (Zipper.Walk.walk r []))).
    { unfold Warblre.utils.List.List.Indexing.Nat.indexing, Result.Conversions.from_option in E.
      destruct (nth_error _ (i - 1)) eqn:E'; [injection E as <-; eauto using nth_error_In | discriminate]. }
    apply filter_In in IN as []; destruct n; try discriminate.
    unfold StaticSemantics.nth_group, StaticSemantics.nth_group_in,
      StaticSemantics.all_groups_in, indexing; cbn.
    destruct (Nat.eqb_spec i 0); [lia | rewrite E; eauto].
  Qed.

  Lemma compilePattern_valid wr rer m input index ms:
      StaticSemantics.countLeftCapturingParensWithin wr nil
      = RegExpRecord.capturingGroupsCount rer ->
      EarlyErrors.Pass_Regex wr nil ->
      Semantics.compilePattern wr rer = Success m ->
      m input index = Success (Some ms) ->
      Match.MatchState.Valid input rer ms.
  Proof.
    intros CAPS EE COMP RUN; unfold Semantics.compilePattern in COMP.
    destruct (Semantics.compileSubPattern wr nil rer forward) as [m0|] eqn:SUB; [|discriminate].
    injection COMP as <-; cbn in RUN.
    destruct (Nat.leb_spec0 index (length input)); cbn in RUN; [|discriminate].
    pose proof Match.MatcherInvariant.compileSubPattern wr rer CAPS EE wr nil
      (Zipper.Root.id wr) forward m0 SUB as MI.
    assert (V0: Match.MatchState.Valid input rer (Notation.match_state input (Z.of_nat index)
                  (List.repeat None (RegExpRecord.capturingGroupsCount rer))))
      by (repeat split; cbn; try lia; auto using repeat_length;
          apply Warblre.utils.List.List.Forall.repeat; constructor).
    destruct (MI _ (fun y => Coercions.wrap_option MatchError Notation.MatchState
                               (Coercions.MatchState_or_failure y)) V0)
      as [FAIL|(y & Vy & _ & EQ)]; [rewrite FAIL in RUN; discriminate|].
    rewrite <- EQ in RUN; cbn in RUN; injection RUN as <-; exact Vy.
  Qed.

  Context (S: Parameters.String).
  Context {laws: StringLaws}.

  Notation str := (String.to_char_list S).

  Lemma regExpBuiltinExec_sticky R res:
      RegExpFlags.y (RegExpInstance.originalFlags R) = true ->
      RegExpInstance.lastIndex R = 0%Z ->
      RegExpInstance.regExpMatcher R str 0 = Success res ->
      ((exists R', regExpBuiltinExec R S = Success (Null R')) <-> res = None).
  Proof.
    intros STICKY LAST MATCH; unfold regExpBuiltinExec.
    rewrite LAST, STICKY, Bool.andb_false_r, (Nat.add_comm _ 2); simpl.
    rewrite MATCH; cbn [Result.bind]; destruct res as [ms|];
      [|rewrite EqDec.reflb; split; [auto | intros _; eexists; reflexivity]].
    split; [intros [R' NULL]; revert NULL | easy].
    repeat match goal with
           | _ => progress cbn [Result.bind negb]
           | _ => rewrite (proj2 (EqDec.inversion_false _ _)) by discriminate
           | [ |- context [ Result.bind ?x _ ] ] => destruct x
           | [ |- context [ if ?b then _ else _ ] ] => destruct b end; easy.
  Qed.

  Lemma from_int_ok (z: Z): (0 <= z)%Z ->
      (NonNegInt.from_int z: Result.Result _ MatchError) = Success (Z.to_nat z).
  Proof. intro LE; unfold NonNegInt.from_int; now rewrite (proj2 (Z.geb_le z 0) LE). Qed.

  Lemma char_pos_le: forall i j, i <= j -> char_pos S i <= char_pos S j.
  Proof.
    induction 1 as [|j _ IH]; [reflexivity|];
      pose proof advanceStringIndex_progress S (char_pos S j); cbn; lia.
  Qed.

  Lemma getStringIndex_mono i j: i <= j -> j <= length str ->
      String.getStringIndex S i <= String.getStringIndex S j.
  Proof. intros; rewrite !getStringIndex_char_pos by lia; now apply char_pos_le. Qed.

  Lemma getStringIndex_length i:
      i <= length str -> String.getStringIndex S i <= String.length S.
  Proof.
    intro; rewrite <- advanceStringIndex_end, <- getStringIndex_char_pos by lia;
      apply getStringIndex_mono; lia.
  Qed.

  Lemma getMatchString_ok a b: a <= b -> b <= String.length S ->
      getMatchString S (MatchRecord.mk a b) = Success (String.substring S a b).
  Proof.
    intros AB BS; unfold getMatchString; cbn;
      rewrite (proj2 (Nat.leb_le _ _) AB), (proj2 (Nat.leb_le _ _) BS); reflexivity.
  Qed.

  Lemma getMatchIndexPair_ok a b: a <= b -> b <= String.length S ->
      getMatchIndexPair S (MatchRecord.mk a b) = Success (a, b).
  Proof.
    intros AB BS; unfold getMatchIndexPair; cbn;
      rewrite (proj2 (Nat.leb_le _ _) AB), (proj2 (Nat.leb_le _ _) BS); reflexivity.
  Qed.

  Lemma capture_to_record_ok c: Match.CaptureRange.Valid str c ->
      capture_to_record S c = Success (capture_record S c).
  Proof.
    inversion 1; subst; cbn; [|reflexivity].
    unfold Match.IteratorOn, match_record in *; rewrite !from_int_ok by lia; cbn.
    rewrite (proj2 (Nat.leb_le _ _)) by (apply getStringIndex_mono; lia); reflexivity.
  Qed.

  Lemma capture_to_value_ok c: Match.CaptureRange.Valid str c ->
      capture_to_value S c = Success (capture_substring S c).
  Proof.
    inversion 1; subst; cbn; [|reflexivity].
    unfold Match.IteratorOn, match_record in *; rewrite !from_int_ok by lia; cbn.
    rewrite (proj2 (Nat.leb_le _ _)) by (apply getStringIndex_mono; lia); cbn.
    rewrite getMatchString_ok
      by (solve [apply getStringIndex_mono; lia | apply getStringIndex_length; lia]);
      reflexivity.
  Qed.

  Lemma capture_record_pair c: Match.CaptureRange.Valid str c ->
    forall mr, capture_record S c = Some mr ->
      exists p, getMatchIndexPair S mr = Success p.
  Proof.
    inversion 1; subst; cbn; intros mr E; [injection E as <-|discriminate].
    unfold Match.IteratorOn in *; eexists; apply getMatchIndexPair_ok;
      [apply getStringIndex_mono; lia | apply getStringIndex_length; lia].
  Qed.

  Notation WForall := (@Warblre.utils.List.List.Forall.Forall _ MatchError _).

  Lemma captures_to_array_ok: forall cs, WForall cs (Match.CaptureRange.Valid str) ->
      captures_to_array S cs = Success (List.map (capture_substring S) cs).
  Proof.
    induction cs as [|c cs IH]; intro F; cbn [captures_to_array List.map]; [reflexivity|].
    apply Warblre.utils.List.List.Forall.cons_inv in F as [Vc F].
    rewrite (capture_to_value_ok c Vc), (IH F); reflexivity.
  Qed.

  Lemma captures_to_indices_ok: forall cs, WForall cs (Match.CaptureRange.Valid str) ->
      captures_to_indices S cs = Success (List.map (capture_record S) cs).
  Proof.
    induction cs as [|c cs IH]; intro F; cbn [captures_to_indices List.map]; [reflexivity|].
    apply Warblre.utils.List.List.Forall.cons_inv in F as [Vc F].
    rewrite (capture_to_record_ok c Vc), (IH F); reflexivity.
  Qed.

  Lemma makeMatchIndicesArray_ok: forall cs, WForall cs (Match.CaptureRange.Valid str) ->
      exists v, makeMatchIndicesArray S (List.map (capture_record S) cs) = Success v.
  Proof.
    induction cs as [|c cs IH]; intro F; cbn [List.map makeMatchIndicesArray]; [eauto|].
    apply Warblre.utils.List.List.Forall.cons_inv in F as [Vc F].
    destruct (capture_record S c) as [mr|] eqn:E; cbn [Result.bind];
      [destruct (capture_record_pair c Vc mr E) as [p ->]; cbn [Result.bind]|];
      destruct (IH F) as [v ->]; cbn [Result.bind]; eauto.
  Qed.

  Lemma makeMatchIndicesGroupList_ok: forall cs gns,
      WForall cs (Match.CaptureRange.Valid str) -> length gns = length cs ->
      exists v, makeMatchIndicesGroupList S (List.map (capture_record S) cs) gns = Success v.
  Proof.
    induction cs as [|c cs IH]; intros [|gn gns] F LEN; cbn [length] in LEN; try discriminate;
      cbn [List.map makeMatchIndicesGroupList]; [eauto..|].
    apply Warblre.utils.List.List.Forall.cons_inv in F as [Vc F].
    destruct (capture_record S c) as [mr|] eqn:E; cbn [Result.bind];
      [destruct (capture_record_pair c Vc mr E) as [p ->]; cbn [Result.bind]|];
      destruct (IH gns F ltac:(lia)) as [v ->]; cbn [Result.bind]; destruct gn; eauto.
  Qed.

  Lemma MakeMatchIndicesGroups_ok mr cs gns hasGroups:
      WForall cs (Match.CaptureRange.Valid str) -> length gns = length cs ->
      exists v,
        MakeMatchIndicesGroups S (mr :: List.map (capture_record S) cs) gns hasGroups
        = Success v.
  Proof.
    intros F LEN; unfold MakeMatchIndicesGroups; cbn [length].
    rewrite length_map, Nat.sub_succ, Nat.sub_0_r, LEN, Nat.eqb_refl;
      cbn [Result.bind negb].
    destruct hasGroups; [|eauto].
    destruct (makeMatchIndicesGroupList_ok cs gns F LEN) as [v ->]; cbn [Result.bind]; eauto.
  Qed.

  (* Group names are read by position, starting at [i]. *)
  Lemma captures_ok (r: Patterns.Regex): forall cs i,
      WForall cs (Match.CaptureRange.Valid str) -> 1 <= i ->
      i + length cs <= 1 + StaticSemantics.countLeftCapturingParensWithin_impl r ->
      (exists v, captures_to_groupnames r cs i = Success v /\ length v = length cs)
      /\ (exists v, captures_to_groupsmap r S cs i = Success v).
  Proof.
    induction cs as [|c cs IH]; intros i F LO HI;
      cbn [captures_to_groupnames captures_to_groupsmap length] in *; [eauto 10|].
    apply Warblre.utils.List.List.Forall.cons_inv in F as [Vc F].
    rewrite (capture_to_value_ok c Vc).
    destruct (nth_group_ok r i ltac:(lia)) as (gn & ? & ? & ->),
             (IH (i + 1) F ltac:(lia) ltac:(lia)) as [(? & -> & LN) [? ->]].
    destruct gn; cbn; repeat split; try (eexists; split; [reflexivity | cbn; lia]); eauto.
  Qed.

  Local Ltac finish_exotic LENC :=
    unfold captures_to_groups_map, captures_to_group_names, match_record;
    rewrite from_int_ok by lia; cbn [Result.bind];
    rewrite LENC, Nat.eqb_refl, (proj2 (Nat.leb_le _ _)) by lia; cbn [Result.bind negb];
    rewrite getMatchString_ok by solve [lia | apply getStringIndex_length; lia];
    cbn [Result.bind]; rewrite captures_to_array_ok by eassumption;
    cbn [Result.bind length]; rewrite length_map, LENC, Nat.add_1_r, Nat.eqb_refl; cbn [negb];
    edestruct captures_ok as [(gns & -> & LGN) [? ->]]; [eassumption | lia | lia |];
    rewrite captures_to_indices_ok by eassumption; cbn [Result.bind];
    rewrite getMatchIndexPair_ok by solve [lia | apply getStringIndex_length; lia];
    edestruct makeMatchIndicesArray_ok as [? ->]; [eassumption|];
    edestruct MakeMatchIndicesGroups_ok as [? ->]; [eassumption | exact LGN |];
    destruct (StaticSemantics.defines_groups _), (RegExpFlags.d _); cbn [Result.bind];
      (do 2 eexists; split; [reflexivity | cbn; repeat split; reflexivity]).

  Lemma regExpBuiltinExec_sticky_exotic R ms:
      RegExpFlags.y (RegExpInstance.originalFlags R) = true ->
      RegExpInstance.lastIndex R = 0%Z ->
      RegExpInstance.regExpMatcher R str 0 = Success (Some ms) ->
      Match.MatchState.Valid str (RegExpInstance.regExpRecord R) ms ->
      StaticSemantics.countLeftCapturingParensWithin_impl (RegExpInstance.originalSource R)
      = RegExpRecord.capturingGroupsCount (RegExpInstance.regExpRecord R) ->
      exists A R',
        regExpBuiltinExec R S = Success (Exotic A R') /\
        ExecArrayExotic.index A = 0 /\
        ExecArrayExotic.input A = S /\
        ExecArrayExotic.array A
        = Some (match_substring S ms)
          :: List.map (capture_substring S) (Notation.MatchState.captures ms).
  Proof.
    intros STICKY LAST MATCH (_ & (? & ?) & LENC & VCAPS) CAPS.
    unfold regExpBuiltinExec.
    rewrite LAST, STICKY, Bool.andb_false_r, (Nat.add_comm _ 2); simpl; rewrite MATCH; cbn [Result.bind].
    rewrite (proj2 (EqDec.inversion_false _ _)) by discriminate; cbn [Result.bind negb].
    rewrite Bool.orb_true_r; cbn [RegExpInstance.setLastIndex
      RegExpInstance.originalSource RegExpInstance.originalFlags RegExpInstance.regExpRecord].
    finish_exotic LENC.
  Qed.

  Lemma none_iff_false {A} (res: option A) (b: bool):
      (res <> None <-> b = true) -> (res = None <-> b = false).
  Proof.
    intros [F G]; destruct res; split; intro H;
      solve [discriminate | reflexivity | pose proof F ltac:(discriminate); congruence
            |apply Bool.not_true_iff_false; intro BT; exact (G BT eq_refl)].
  Qed.

  Lemma exec_null_exotic (R: RegExpInstance) (res: option Notation.MatchState):
      exec_agrees R S res ->
      ((exists inst', regExpExec R S = Success (Null inst')) <-> res = None) /\
      ((exists A inst', regExpExec R S = Success (Exotic A inst')) <-> res <> None).
  Proof.
    intro ARR; unfold exec_agrees in ARR;
      destruct (regExpExec R S) as [[|]|], res; try contradiction;
      split; split; intro H;
      solve [eauto | congruence | destruct H as (? & [=]) | destruct H as (? & ? & [=])].
  Qed.

  (* [List.tl] skips [exec]'s array whole-match substring at position 0. *)
  Lemma exec_array_transfer
      (P: list bool -> Prop) (Q: Prop) (R: RegExpInstance) (res: option Notation.MatchState):
      exec_agrees R S res ->
      match res with
      | Some ms => P (defined_bits (Notation.MatchState.captures ms))
      | None => Q
      end ->
      match regExpExec R S with
      | Success (Null _) => Q
      | Success (Exotic A _) => P (defined_bits (List.tl (ExecArrayExotic.array A)))
      | _ => False
      end.
  Proof.
    intros ARR ANS; unfold exec_agrees in ARR; destruct res, (regExpExec R S) as [[|]|];
      try contradiction; [|exact ANS].
    destruct ARR as (_ & _ & ->); cbn [List.tl];
      rewrite <- (defined_bits_captures S) in ANS; exact ANS.
  Qed.


  Section FromMatcher.
    Context (wr: Patterns.Regex) (flags: RegExpFlags) (rer: RegExpRecord).
    Context (m: list Parameters.Character -> non_neg_integer -> Notation.MatchResult).
    Hypothesis EE: EarlyErrors.Pass_Regex wr nil.
    Hypothesis COMP: Semantics.compilePattern wr rer = Success m.
    Hypothesis RER: rer = rer_of wr flags.

    Let inst := reg_exp_instance wr flags rer m 0%Z.

    Lemma exec_initialize: regExpInitialize wr flags = Success inst.
    Proof. unfold regExpInitialize, inst, rer_of in *; now rewrite <- RER, COMP. Qed.

    Local Lemma inst_valid i ms:
        m str i = Success (Some ms) -> Match.MatchState.Valid str rer ms.
    Proof. intro; eapply compilePattern_valid; eauto; now rewrite RER. Qed.

    Local Lemma inst_caps:
      StaticSemantics.countLeftCapturingParensWithin_impl (RegExpInstance.originalSource inst)
      = RegExpRecord.capturingGroupsCount (RegExpInstance.regExpRecord inst).
    Proof. cbn; now rewrite RER. Qed.

    Lemma exec_sticky:
      RegExpFlags.y flags = true ->
      forall res, m str 0 = Success res -> exec_agrees inst S res.
    Proof.
      intros STICKY [ms|] MATCH; unfold exec_agrees, regExpExec.
      - edestruct regExpBuiltinExec_sticky_exotic with (R := inst) (ms := ms)
          as (? & ? & -> & EQ);
          cbn; solve [exact EQ | assumption | reflexivity | apply inst_caps
                     | eauto using inst_valid].
      - destruct (proj2 (regExpBuiltinExec_sticky inst None ltac:(cbn; assumption)
                           ltac:(reflexivity) MATCH) eq_refl) as [? ->]; exact I.
    Qed.

  End FromMatcher.

End ExecSucceeds.

