From Linden Require Import Tree Parameters Regex Semantics Chars StrictSuffix.
From Warblre Require Import Base.
From Linden Require Import Tactics.
Require Import List Lia.
Import ListNotations.

Section MembershipProof.
  Context {params: LindenParameters}.

  Fixpoint readDepth_tr (t: tree) := match t with
  | Mismatch | Match => 1
  | Choice t1 t2 => 1 + max (readDepth_tr t1) (readDepth_tr t2)
  | Read _ _ => 1
  | ReadBackRef str t =>
    match str with
    | nil => 1 + readDepth_tr t
    | _ => 1
    end
  | Progress t => 1 + readDepth_tr t
  | AnchorPass _ t => 1 + readDepth_tr t
  | GroupAction _ t => 1 + readDepth_tr t
  | LK _ _ t => 1 + readDepth_tr t
  | LKFail _ _ => 1
  end.

  (* The subset of supported regexes: no lookarounds, no forced quantifiers *)
  Inductive supported_regex: regex -> Prop :=
  | s_Epsilon: supported_regex Epsilon
  | s_Character: forall cd, supported_regex (Regex.Character cd)
  | s_Disjunction: forall r1 r2, supported_regex r1 -> supported_regex r2 -> supported_regex (Disjunction r1 r2)
  | s_Sequence: forall r1 r2, supported_regex r1 -> supported_regex r2 -> supported_regex (Sequence r1 r2)
  | s_Quantified: forall greedy delta r, supported_regex r -> supported_regex (Quantified greedy 0 delta r) (* min = 0 *)
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
  | Quantified _ _ _ r => 3 + regex_size r (* Choice, Reset, Check; this is an overapproximation for done quantifiers *)
  | Lookaround _ r => 1 + regex_size r
  | Group _ r => 2 + regex_size r (* Open, Close *)
  | Anchor _ | Backreference _ => 1
  end.


  (* First version of read depth: with actions only *)
  Fixpoint readDepth_act (l: actions): nat := match l with
  | [] => 1
  | Acheck _ :: l => 1 + readDepth_act l (* Without the input, we can't know if the check succeeds *)
  | Aclose _ :: l => 1 + readDepth_act l
  | Areg (Quantified _ 0 (NoI.N 0) r) :: l => readDepth_act l
  | Areg (Quantified _ _ _ r) :: l => max (3 + regex_size r) (1 + readDepth_act l)
  (* This formula is invalid for forced quantifiers, but those are unsupported here *)
  | Areg r :: l => regex_size r + readDepth_act l
  (* We could have predicted this in a slightly finer way: when encountering
  a Character regex, we could have returned 1 *)
  (* But we can't do the same for backreferences, because we don't have the
  group map *)
  end.

  Definition decide_nat_NoI_eq_zero (n: nat) (m: non_neg_integer_or_inf):
    {(n, m) = (0, NoI.N 0)} + {(n, m) <> (0, NoI.N 0)}.
  Proof.
    destruct n.
    - destruct m.
      + destruct n.
        * left. reflexivity.
        * right. discriminate.
      + right. discriminate.
    - right. discriminate.
  Defined.

  Lemma readDepth_act_reg_le:
    forall r l, readDepth_act (Areg r :: l) <= regex_size r + readDepth_act l.
  Proof.
    intros r l. destruct r; try solve[simpl; auto].
    destruct (decide_nat_NoI_eq_zero min delta).
    - injection e as -> ->. simpl. lia.
    - replace (readDepth_act (_ :: l)) with (max (3 + regex_size r) (1 + readDepth_act l)).
    2: {
      symmetry. destruct min; destruct delta as [[]|]; try contradiction; reflexivity.
    }
    simpl regex_size. lia.
  Qed.
  
  Lemma readDepth_tr_bound:
    forall rer l inp gm t,
      supported_actions l -> is_tree rer l inp gm forward t ->
        readDepth_tr t <= readDepth_act l.
  Proof.
    intros rer l inp gm t. remember forward as dir.
    induction 2.
    - simpl. reflexivity.
    - simpl. inversion H; subst.
      specialize (IHis_tree eq_refl H4). lia.
    - simpl. lia.
    - simpl. inversion H; subst.
      specialize (IHis_tree eq_refl H4). lia.
    - simpl. inversion H; subst.
      specialize (IHis_tree eq_refl H4). lia.
    - simpl. lia.
    - simpl. lia.
    - (* Disjunction *)
      inversion H; subst. inversion H2; subst. inversion H1; subst.
      specialize (IHis_tree2 eq_refl).
      specialize_prove IHis_tree2. {
        constructor; auto. constructor; auto.
      }
      specialize (IHis_tree1 eq_refl).
      specialize_prove IHis_tree1. {
        constructor; auto. constructor; auto.
      }
      pose proof readDepth_act_reg_le r2 cont. pose proof readDepth_act_reg_le r1 cont.
      simpl. lia.
    - (* Sequence *)
      subst dir. simpl seq_list in *.
      inversion H; subst. inversion H3; subst. inversion H2; subst.
      specialize (IHis_tree eq_refl).
      specialize_prove IHis_tree. {
        constructor. 1: constructor; auto.
        constructor; [constructor|]; auto.
      }
      simpl "++" in IHis_tree.
      pose proof readDepth_act_reg_le r1 (Areg r2 :: cont).
      pose proof readDepth_act_reg_le r2 cont.
      simpl. lia.
    - (* Forced quantifier: unsupported *)
      inversion H; subst. inversion H3; subst. inversion H2.
    - inversion H; subst. simpl. apply IHis_tree; auto.
    - (* Free quantifier: blocking *)
      subst.
      replace (readDepth_act (Areg _ :: cont)) with (max (3 + regex_size r1) (1 + readDepth_act cont)).
      2: {
        symmetry. simpl. destruct plus; reflexivity.
      }
      (* Specializing the induction hypotheses *)
      inversion H; subst. inversion H2; subst. inversion H1; subst.
      specialize (IHis_tree2 eq_refl H3).
      specialize (IHis_tree1 eq_refl).
      specialize_prove IHis_tree1. {
        repeat (constructor; auto).
      }
      replace (readDepth_tr _) with (max (2 + readDepth_tr titer) (1 + readDepth_tr tskip)).
      2: {
        destruct greedy; simpl. 1: reflexivity.
        destruct (readDepth_tr tskip); simpl; lia.
      }
      (* Here, we are blocked *)
      (* Intuitively, the read depth of titer is at most 1 + regex_size r1
      but the induction hypothesis IHis_tree1 does not give us that *)
  Abort.



  (* Second version of read depth: with actions and inputs *)
  (* The input does not change, even when there is a read: inp is to be
  understood as the initial input passed to readDepth_inp_act *)
  Fixpoint readDepth_inp_act (inp: input) (l: actions): nat :=
    match l with
    | [] => 1
    | Aclose _ :: l => 1 + readDepth_inp_act inp l
    | Acheck inpcheck :: l =>
        if is_strict_suffix inp inpcheck forward then
          1 + readDepth_inp_act inp l
        else
          1
    | Areg (Quantified _ 0 (NoI.N 0) r) :: l => readDepth_inp_act inp l
    | Areg (Quantified _ _ _ r) :: l => max (3 + regex_size r) (1 + readDepth_inp_act inp l)
    | Areg r :: l => regex_size r + readDepth_inp_act inp l
    (* We could have predicted this in a slightly finer way: when encountering
    a Character regex, we could have returned 1 *)
    (* But we can't do the same for backreferences, because we don't have the
    group map *)
    end.

  Lemma readDepth_inp_act_reg_le:
    forall inp r l, readDepth_inp_act inp (Areg r :: l) <= regex_size r + readDepth_inp_act inp l.
  Proof.
    intros inp r l. destruct r; try solve[simpl; auto].
    destruct (decide_nat_NoI_eq_zero min delta).
    - injection e as -> ->. simpl. lia.
    - replace (readDepth_inp_act inp (_ :: l)) with (max (3 + regex_size r) (1 + readDepth_inp_act inp l)).
    2: {
      symmetry. destruct min; destruct delta as [[]|]; try contradiction; reflexivity.
    }
    simpl regex_size. lia.
  Qed.

  Lemma readDepth_tr_bound_inp_act:
    forall rer l inp gm t,
      supported_actions l -> is_tree rer l inp gm forward t ->
        readDepth_tr t <= readDepth_inp_act inp l.
  Proof.
    intros rer l inp gm t. remember forward as dir.
    induction 2.
    - simpl. reflexivity.
    - simpl. inversion H; subst.
      specialize (IHis_tree eq_refl H4).
      apply is_strict_suffix_correct in PROGRESS. rewrite PROGRESS. lia.
    - simpl. destruct is_strict_suffix; lia.
    - simpl. inversion H; subst.
      specialize (IHis_tree eq_refl H4). lia.
    - simpl. inversion H; subst.
      specialize (IHis_tree eq_refl H4). lia.
    - simpl. lia.
    - simpl. lia.
    - (* Disjunction *)
      inversion H; subst. inversion H2; subst. inversion H1; subst.
      specialize (IHis_tree2 eq_refl).
      specialize_prove IHis_tree2. {
        constructor; auto. constructor; auto.
      }
      specialize (IHis_tree1 eq_refl).
      specialize_prove IHis_tree1. {
        constructor; auto. constructor; auto.
      }
      pose proof readDepth_inp_act_reg_le inp r2 cont. pose proof readDepth_inp_act_reg_le inp r1 cont.
      simpl. lia.
    - (* Sequence *)
      subst dir. simpl seq_list in *.
      inversion H; subst. inversion H3; subst. inversion H2; subst.
      specialize (IHis_tree eq_refl).
      specialize_prove IHis_tree. {
        constructor. 1: constructor; auto.
        constructor; [constructor|]; auto.
      }
      simpl "++" in IHis_tree.
      pose proof readDepth_inp_act_reg_le inp r1 (Areg r2 :: cont).
      pose proof readDepth_inp_act_reg_le inp r2 cont.
      simpl. lia.
    - (* Forced quantifier: unsupported *)
      inversion H; subst. inversion H3; subst. inversion H2.
    - inversion H; subst. simpl. apply IHis_tree; auto.
    - (* Free quantifier *)
      subst.
      replace (readDepth_inp_act inp (_ :: cont)) with (max (3 + regex_size r1) (1 + readDepth_inp_act inp cont)).
      2: {
        symmetry. simpl. destruct plus; reflexivity.
      }
      replace (readDepth_tr _) with (max (2 + readDepth_tr titer) (1 + readDepth_tr tskip)).
      2: {
        destruct greedy; simpl. 1: reflexivity.
        destruct (readDepth_tr tskip); simpl; lia.
      }
      (* Specializing the induction hypotheses *)
      inversion H; subst. inversion H2; subst. inversion H1; subst.
      specialize (IHis_tree2 eq_refl H3).
      specialize (IHis_tree1 eq_refl).
      specialize_prove IHis_tree1. {
        repeat (constructor; auto).
      }
      pose proof readDepth_inp_act_reg_le inp r1 (Acheck inp :: Areg (Quantified greedy 0 plus r1) :: cont).
      simpl readDepth_inp_act at 2 in H0.
      replace (is_strict_suffix inp inp forward) with false in H0.
      2: {
        symmetry. apply is_strict_suffix_inv_false.
        intro ABS. apply (ss_neq inp inp forward ABS). reflexivity.
      }
      lia.
    - (* Group action *)
      simpl.
      subst dir.
      inversion H; subst. inversion H3; subst. inversion H2; subst.
      specialize (IHis_tree eq_refl).
      specialize_prove IHis_tree. {
        repeat (constructor; auto).
      }
      pose proof readDepth_inp_act_reg_le inp r1 (Aclose gid :: cont).
      simpl readDepth_inp_act at 2 in H1. lia.
    - inversion H; subst. inversion H2; subst. inversion H1.
    - inversion H; subst. inversion H3; subst. inversion H2.
    - simpl. inversion H; subst.
      specialize (IHis_tree eq_refl H4). lia.
    - simpl. lia.
    - simpl. destruct br_str as [|x br_str_tl].
      + assert (nextinp = inp) by admit. (* because the backreference read nothing*)
        subst nextinp.
        inversion H; subst. specialize (IHis_tree eq_refl H4). lia.
      + lia.
    - simpl. lia.
  Admitted.

  (* Formalizing when a list of actions comes from a supported regex (forward direction only) *)
  Inductive act_from_regex (r: regex): actions -> Prop :=
  | afr_refl: act_from_regex r [Areg r]
  | afr_pop_check: forall inpcheck l,
      act_from_regex r (Acheck inpcheck :: l) -> act_from_regex r l
  | afr_pop_close: forall gid l,
      act_from_regex r (Aclose gid :: l) -> act_from_regex r l
  | afr_pop_epsilon: forall l,
      act_from_regex r (Areg Epsilon :: l) -> act_from_regex r l
  | afr_pop_char: forall cd l,
      act_from_regex r (Areg (Regex.Character cd) :: l) -> act_from_regex r l
  | afr_pop_disj_l: forall r1 r2 l,
      act_from_regex r (Areg (Disjunction r1 r2) :: l) -> act_from_regex r (Areg r1 :: l)
  | afr_pop_disj_r: forall r1 r2 l,
      act_from_regex r (Areg (Disjunction r1 r2) :: l) -> act_from_regex r (Areg r2 :: l)
  | afr_pop_sequence: forall r1 r2 l,
      act_from_regex r (Areg (Sequence r1 r2) :: l) -> act_from_regex r (Areg r1 :: Areg r2 :: l)
  | afr_pop_quant_done: forall greedy r1 l,
      act_from_regex r (Areg (Quantified greedy 0 (NoI.N 0) r1) :: l) -> act_from_regex r l
  | afr_pop_quant_free_iter: forall greedy delta r1 inp l,
      act_from_regex r (Areg (Quantified greedy 0 (NoI.N 1 + delta)%NoI r1) :: l) -> act_from_regex r (Areg r1 :: Acheck inp :: Areg (Quantified greedy 0 delta r1) :: l)
  | afr_pop_quant_free_skip: forall greedy delta r1 l,
      act_from_regex r (Areg (Quantified greedy 0 (NoI.N 1 + delta)%NoI r1) :: l) -> act_from_regex r l
  | afr_pop_group: forall gid r1 l,
      act_from_regex r (Areg (Group gid r1) :: l) -> act_from_regex r (Areg r1 :: Aclose gid :: l)
  | afr_pop_anchor: forall a l,
      act_from_regex r (Areg (Anchor a) :: l) -> act_from_regex r l
  | afr_pop_backref: forall gid l,
      act_from_regex r (Areg (Backreference gid) :: l) -> act_from_regex r l.
  
  Lemma readDepth_inp_act_bound:
    forall act r, act_from_regex r act ->
      forall inp, readDepth_inp_act inp act <= 3*regex_size r + 1.
  Proof.
    induction 1.
    - intro inp. pose proof readDepth_inp_act_reg_le inp r [].
      simpl readDepth_inp_act at 2 in H. lia.
    - intro inp.
      (* Blocked! *)
      (* IHact_from_regex with an input that is a strict suffix if inpcheck gives what we want *)
      (* but if inp is equal to inpcheck,  *)
    

End MembershipProof.