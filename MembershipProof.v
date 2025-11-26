From Linden Require Import Regex Parameters Semantics Chars StrictSuffix
  FunctionalSemantics Tactics.
From Warblre Require Import Base.
Require Import List Lia.
Import ListNotations.

Section MembershipProof.
  Context {params: LindenParameters}.

  (* The subset of supported regexes: no lookarounds, no forced quantifiers *)
  Inductive supported_regex: regex -> Prop :=
  | s_Epsilon: supported_regex Epsilon
  | s_Character: forall cd, supported_regex (Regex.Character cd)
  | s_Disjunction: forall r1 r2, supported_regex r1 -> supported_regex r2 -> supported_regex (Disjunction r1 r2)
  | s_Sequence: forall r1 r2, supported_regex r1 -> supported_regex r2 -> supported_regex (Sequence r1 r2)
  | s_Quantified: forall greedy r, supported_regex r -> supported_regex (Quantified greedy 0 +∞ r) (* only the star (greedy or lazy) *)
  (* No lookaround *)
  | s_Group: forall gid r, supported_regex r -> supported_regex (Group gid r)
  | s_Anchor: forall a, supported_regex (Anchor a)
  | s_Backreference: forall gid, supported_regex (Backreference gid).

  (* Lifting to lists of actions *)
  Inductive supported_action: action -> Prop :=
  | s_Acheck: forall i, supported_action (Acheck i)
  | s_Aclose: forall g, supported_action (Aclose g)
  | s_Areg: forall r, supported_regex r -> supported_action (Areg r).

  Definition supported_actions (l: actions): Prop := Forall supported_action l.

  Fixpoint regex_size (r: regex): nat := match r with
  | Epsilon | Regex.Character _ => 1
  | Disjunction r1 r2 | Sequence r1 r2 => 1 + regex_size r1 + regex_size r2
  | Quantified _ _ _ r => 3 + regex_size r
  | Lookaround _ r => 1 + regex_size r
  | Group _ r => 2 + regex_size r (* Open, Close *)
  | Anchor _ | Backreference _ => 1
  end.

  (* Formalizing when an input and list of actions come from a supported regex (forward direction only) *)
  Inductive act_from_regex (r: regex): input -> actions -> Prop :=
  | afr_refl: forall inp, act_from_regex r inp [Areg r]
  | afr_pop_check: forall inp inpcheck l,
      strict_suffix inp inpcheck forward ->
      act_from_regex r inp (Acheck inpcheck :: l) ->
      act_from_regex r inp l
  | afr_pop_close: forall inp gid l,
      act_from_regex r inp (Aclose gid :: l) -> act_from_regex r inp l
  | afr_pop_epsilon: forall inp l,
      act_from_regex r inp (Areg Epsilon :: l) -> act_from_regex r inp l
  | afr_pop_char: forall inp nextinp cd l,
      act_from_regex r inp (Areg (Regex.Character cd) :: l) ->
      advance_input inp forward = Some nextinp ->
      act_from_regex r nextinp l
  | afr_pop_disj_l: forall inp r1 r2 l,
      act_from_regex r inp (Areg (Disjunction r1 r2) :: l) ->
      act_from_regex r inp (Areg r1 :: l)
  | afr_pop_disj_r: forall inp r1 r2 l,
      act_from_regex r inp (Areg (Disjunction r1 r2) :: l) ->
      act_from_regex r inp (Areg r2 :: l)
  | afr_pop_sequence: forall inp r1 r2 l,
      act_from_regex r inp (Areg (Sequence r1 r2) :: l) ->
      act_from_regex r inp (Areg r1 :: Areg r2 :: l)
  | afr_pop_quant_done: forall inp greedy r1 l,
      act_from_regex r inp (Areg (Quantified greedy 0 (NoI.N 0) r1) :: l) ->
      act_from_regex r inp l
  | afr_pop_quant_free_iter: forall greedy delta r1 inp l,
      act_from_regex r inp (Areg (Quantified greedy 0 (NoI.N 1 + delta)%NoI r1) :: l) ->
      act_from_regex r inp (Areg r1 :: Acheck inp :: Areg (Quantified greedy 0 delta r1) :: l)
  | afr_pop_quant_free_skip: forall inp greedy delta r1 l,
      act_from_regex r inp (Areg (Quantified greedy 0 (NoI.N 1 + delta)%NoI r1) :: l) ->
      act_from_regex r inp l
  | afr_pop_group: forall inp gid r1 l,
      act_from_regex r inp (Areg (Group gid r1) :: l) ->
      act_from_regex r inp (Areg r1 :: Aclose gid :: l)
  | afr_pop_anchor: forall inp a l,
      act_from_regex r inp (Areg (Anchor a) :: l) ->
      act_from_regex r inp l
  | afr_pop_backref: forall inp n nextinp gid l,
      act_from_regex r inp (Areg (Backreference gid) :: l) ->
      advance_input_n inp n forward = nextinp ->
      act_from_regex r nextinp l.

  Fixpoint first_check_input (act: actions): option input :=
    match act with
    | [] => None
    | Areg _ :: l | Aclose _ :: l => first_check_input l
    | Acheck inp :: _ => Some inp
    end.

  Fixpoint last_chunk_size (act: actions): nat :=
    match act with
    | Acheck _ :: _ => 0 (* should not happen *)
    | Aclose gid :: l => 1 + last_chunk_size l
    | Areg r :: l => regex_size r + last_chunk_size l
    | [] => 0
    end.

  Fixpoint actions_fuel' (inp: input) (act: actions) (checks_pass: bool) {struct act}: nat :=
    match act with
    | Acheck _ :: Areg r :: l =>
      match first_check_input l with
      (* Not last chunk *)
      | Some _ => 2 + actions_fuel' inp l checks_pass
      (* Last chunk *)
      | None =>
          let bonus := if checks_pass then 1 else 0 in
          1 + (bonus + remaining_length inp forward) * last_chunk_size (Areg r :: l)
      end
    | Acheck _ :: _ => 0 (* should not happen *)
    | Areg r :: l => regex_size r + actions_fuel' inp l checks_pass
    | Aclose _ :: l => 1 + actions_fuel' inp l checks_pass
    | [] => 0 (* should not happen *)
    end.
  
  Definition actions_fuel (inp: input) (act: actions): nat :=
    match first_check_input act with
    (* Only one (last) chunk: bonus is one *)
    | None => (1 + remaining_length inp forward) * last_chunk_size act
    (* At least two chunks *)
    | Some inpchk =>
        let b := is_strict_suffix inp inpchk forward in
        match act with
        | Areg (Quantified _ _ _ r) :: l =>
          (if b then 1 else 3 + regex_size r) + actions_fuel' inp l b
        | _ => actions_fuel' inp act b
        end
    end.



  Lemma is_strict_suffix_incr:
    forall inp nextinp inpchk dir,
      advance_input inp dir = Some nextinp ->
      Bool.le (is_strict_suffix inp inpchk dir) (is_strict_suffix nextinp inpchk dir).
  Admitted.

  Lemma actions_fuel'_monotonic_inp:
    forall inp nextinp cont bonus,
      strict_suffix nextinp inp forward ->
      actions_fuel' inp cont bonus >= actions_fuel' nextinp cont bonus.
  Proof.
    intros inp nextinp cont bonus SS. induction cont.
    - simpl. lia.
    - destruct a; simpl; try lia.
      destruct cont as [ | [r | ? | ?] l]; simpl; try lia.
      destruct first_check_input.
      + simpl in IHcont. lia.
      + assert (remaining_length inp forward > remaining_length nextinp forward) by admit.
        pose proof PeanoNat.Nat.mul_le_mono_r ((if bonus then 1 else 0) + remaining_length nextinp forward) ((if bonus then 1 else 0) + remaining_length inp forward) (regex_size r + last_chunk_size l).
        specialize_prove H0 by lia. lia.
  Admitted.

  Lemma actions_fuel'_monotonic_bonus:
    forall inp cont bonus bonus',
      Bool.le bonus bonus' ->
      actions_fuel' inp cont bonus <= actions_fuel' inp cont bonus'.
  Proof.
    intros inp cont bonus bonus' LE. induction cont.
    - simpl. lia.
    - simpl. destruct a; simpl; try lia.
      destruct cont as [|[r | ? | ?] l]; simpl; try lia.
      destruct first_check_input.
      + simpl in IHcont. lia.
      + apply -> PeanoNat.Nat.succ_le_mono.
        apply PeanoNat.Nat.mul_le_mono_r, PeanoNat.Nat.add_le_mono_r.
        destruct bonus; destruct bonus'; simpl in LE; try discriminate; lia.
  Qed.

  Lemma read_decreases_fuel':
    forall inp cd nextinp cont inpchk,
      advance_input inp forward = Some nextinp ->
      actions_fuel' inp (Areg (Regex.Character cd) :: cont) (is_strict_suffix inp inpchk forward) >
      actions_fuel' nextinp cont (is_strict_suffix nextinp inpchk forward).
  Proof.
    intros inp cd nextinp cont inpchk ADV. simpl.
    assert (Bool.le (is_strict_suffix inp inpchk forward) (is_strict_suffix nextinp inpchk forward)) by admit.
    (* assert (SS: strict_suffix nextinp inp forward) by admit. *)
    set (bonus := is_strict_suffix inp inpchk forward) in *.
    set (bonus' := is_strict_suffix nextinp inpchk forward) in *.
    induction cont.
    - simpl. lia.
    - simpl. destruct a; simpl; try lia.
      destruct cont as [|[r | ? | ?] l]; simpl; try lia.
      destruct first_check_input.
      + simpl in IHcont. lia.
      + unfold gt. apply le_lt_S.
        apply -> PeanoNat.Nat.succ_le_mono.
        apply PeanoNat.Nat.mul_le_mono_r.
        assert (remaining_length nextinp forward < remaining_length inp forward) by admit.
        destruct bonus; destruct bonus'; simpl in H; try discriminate; lia.
  Admitted.



  Lemma read_decreases_fuel:
    forall inp cd nextinp cont,
      advance_input inp forward = Some nextinp ->
      actions_fuel inp (Areg (Regex.Character cd) :: cont) > actions_fuel nextinp cont.
  Proof.
    intros inp cd nextinp cont EQ_nextinp.
    unfold actions_fuel. simpl first_check_input.
    destruct first_check_input as [inpchk|].
    - simpl actions_fuel'.
      pose proof read_decreases_fuel' inp cd nextinp cont inpchk EQ_nextinp.
      simpl in H.
      destruct cont as [|[r | ? | ?] l]; simpl in *; try lia.
      destruct r; try lia.
      assert ((if (is_strict_suffix nextinp inpchk forward: bool) then 1 else S (S (S (regex_size r)))) <= regex_size (Quantified greedy min delta r)). {
        simpl. destruct (is_strict_suffix nextinp inpchk forward); lia.
      }
      lia.
    - simpl. unfold gt. apply le_lt_S.
    apply PeanoNat.Nat.add_le_mono_l.
    replace (remaining_length inp forward) with (S (remaining_length nextinp forward)) by admit.
    simpl. lia.
  Admitted.

  Lemma actions_fuel_notlast_le:
    forall inp act inpchk,
      first_check_input act = Some inpchk ->
      actions_fuel inp act <= actions_fuel' inp act (is_strict_suffix inp inpchk forward).
  Proof.
    intros inp act inpchk FSTCHK. unfold actions_fuel.
    rewrite FSTCHK.
    destruct act as [|[r | ? | ?] l]; try reflexivity.
    destruct r; try reflexivity.
    destruct is_strict_suffix; simpl; lia.
  Qed.

  Theorem functional_terminates':
    forall (r: regex) (inp: input) (act: actions),
      supported_regex r -> act_from_regex r inp act ->
      forall fuel, fuel > actions_fuel inp act ->
        forall gm rer, compute_tree rer act inp gm forward fuel <> None.
  Proof.
    intros r inp act SUPP_REGEX AFR fuel.
    revert inp act AFR. induction fuel.
    - lia.
    - intros inp act AFR FUEL gm rer. simpl.
      destruct act as [ | [[] | inpcheck | gid] cont ].
      + discriminate.
      + apply IHfuel.
        { apply afr_pop_epsilon. auto. }
        unfold actions_fuel in FUEL. unfold actions_fuel.
        simpl in FUEL.
        destruct first_check_input as [inpchk|].
        * destruct cont as [|[] cont]; try lia.
          destruct r0; try lia.
          simpl in FUEL.
          destruct is_strict_suffix; lia.
        * lia.
      + destruct read_char as [[c nextinp]|] eqn:READ; try discriminate.
        specialize (IHfuel nextinp cont).
        specialize_prove IHfuel. { apply afr_pop_char with (inp := inp) (cd := cd).
        1: auto. admit. }
        specialize_prove IHfuel. {
          pose proof read_decreases_fuel inp cd nextinp cont.
          specialize_prove H. { eapply read_char_success_advance; eauto. }
          lia.
        }
        specialize (IHfuel gm rer).
        destruct compute_tree as [treecont|]. * discriminate. * contradiction.
      + unfold actions_fuel in FUEL.
        destruct first_check_input as [inpchk|] eqn:FSTCHK.
        * simpl in FSTCHK, FUEL.
          assert (IH1: compute_tree rer (Areg r1 :: cont) inp gm forward fuel <> None). {
            apply IHfuel.
            - eapply afr_pop_disj_l; eauto.
            - pose proof actions_fuel_notlast_le inp (Areg r1 :: cont) inpchk.
              specialize (H FSTCHK).
              simpl in H. lia.
          }
          assert (IH2: compute_tree rer (Areg r2 :: cont) inp gm forward fuel <> None). {
            apply IHfuel.
            - eapply afr_pop_disj_r; eauto.
            - pose proof actions_fuel_notlast_le inp (Areg r2 :: cont) inpchk.
              specialize (H FSTCHK).
              simpl in H. lia.
          }
          destruct (compute_tree rer (Areg r1 :: cont) inp gm forward fuel); try contradiction.
          destruct compute_tree; try contradiction. discriminate.
        * simpl in FSTCHK.
          assert (IH1: compute_tree rer (Areg r1 :: cont) inp gm forward fuel <> None). {
            apply IHfuel.
            - eapply afr_pop_disj_l; eauto.
            - unfold actions_fuel. simpl first_check_input. rewrite FSTCHK.
              simpl last_chunk_size in *.
              unfold gt in FUEL. unfold gt.
              assert ((1 + remaining_length inp forward) * (regex_size r1 + last_chunk_size cont) < (1 + remaining_length inp forward) * S (regex_size r1 + regex_size r2 + last_chunk_size cont)). {
                apply PeanoNat.Nat.mul_lt_mono_pos_l; lia.
              }
              lia.
          }
          assert (IH2: compute_tree rer (Areg r2 :: cont) inp gm forward fuel <> None). {
            apply IHfuel.
            - eapply afr_pop_disj_r; eauto.
            - unfold actions_fuel. simpl first_check_input. rewrite FSTCHK.
              simpl last_chunk_size in *.
              unfold gt in FUEL. unfold gt.
              assert ((1 + remaining_length inp forward) * (regex_size r1 + last_chunk_size cont) < (1 + remaining_length inp forward) * S (regex_size r1 + regex_size r2 + last_chunk_size cont)). {
                apply PeanoNat.Nat.mul_lt_mono_pos_l; lia.
              }
              lia.
          }
          destruct (compute_tree rer (Areg r1 :: cont) inp gm forward fuel); try contradiction.
          destruct compute_tree; try contradiction. discriminate.
      + unfold actions_fuel in FUEL. destruct first_check_input as [inpchk|] eqn:FSTCHK.
        * simpl in FUEL.
          apply IHfuel.
          1: apply afr_pop_sequence; auto.
          pose proof actions_fuel_notlast_le inp (Areg r1 :: Areg r2 :: cont) inpchk FSTCHK.
          simpl in H. lia.
        * simpl last_chunk_size in FUEL.
          apply IHfuel. 1: apply afr_pop_sequence; auto.
          unfold actions_fuel. setoid_rewrite FSTCHK.
          simpl last_chunk_size.
          unfold gt in FUEL. unfold gt.
          assert ((1 + remaining_length inp forward) * (regex_size r1 + (regex_size r2 + last_chunk_size cont)) < (1 + remaining_length inp forward) * S (regex_size r1 + regex_size r2 + last_chunk_size cont)). {
            apply PeanoNat.Nat.mul_lt_mono_pos_l; lia.
          }
          lia.
      + replace min with 0 in * by admit.
        replace delta with +∞ in * by admit.
        simpl noi_pred.
        assert (IHiter: compute_tree rer (Areg r1 :: Acheck inp :: Areg (Quantified greedy 0 +∞ r1) :: cont) inp (Groups.GroupMap.reset (def_groups r1) gm) forward fuel <> None). {
          apply IHfuel.
          - apply afr_pop_quant_free_iter. auto.
          - unfold actions_fuel. simpl first_check_input. cbv match.
            replace (is_strict_suffix inp inp forward) with false by admit.
            destruct (match r1 with Quantified _ _ _ _ => true | _ => false end) eqn:R1_QUANT.
            + destruct r1; try discriminate. simpl actions_fuel'.
              unfold actions_fuel in FUEL. simpl first_check_input in FUEL.
              destruct first_check_input as [inpchk | ].
              * admit. (* HARD *)
              * simpl in FUEL. lia.
            + replace (match r1 with | Quantified _ _ _ r0 => _ | _ => _ end) with (actions_fuel' inp (Areg r1 :: Acheck inp :: Areg (Quantified greedy 0 +∞ r1) :: cont) false).
              2: { destruct r1; try discriminate; reflexivity. }
              unfold actions_fuel in FUEL. simpl first_check_input in FUEL.
              simpl. destruct first_check_input as [inpchk | ].
              * admit. (* HARD *)
              * simpl in *. lia.
        }
        assert (IHskip: compute_tree rer cont inp gm forward fuel <> None). {
          apply IHfuel.
          - eapply afr_pop_quant_free_skip with (greedy := greedy) (delta := +∞). apply AFR.
          - unfold actions_fuel in FUEL.
            simpl first_check_input in FUEL.
            destruct first_check_input as [inpchk | ] eqn:FSTCHK.
            + pose proof actions_fuel_notlast_le inp cont inpchk FSTCHK.
              assert ((if is_strict_suffix inp inpchk forward then 1 else 3 + regex_size r1) >= 1). { destruct (is_strict_suffix inp inpchk forward); lia. }
              lia.
            + simpl in FUEL. unfold actions_fuel. rewrite FSTCHK. simpl. lia.
        }
        destruct compute_tree; try contradiction.
        destruct compute_tree; try contradiction. discriminate.
      + (* No lookarounds *) exfalso. admit.
      + (* Group *)


End MembershipProof.
