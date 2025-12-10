From Linden Require Import Regex Parameters Semantics Chars StrictSuffix
  FunctionalSemantics Tactics.
From Warblre Require Import Base.
Require Import List Lia Sorted.
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


  (* A list of actions coming from a supported regex is a supported list of actions *)
  Lemma suppregex_suppactions:
    forall r, supported_regex r ->
      forall inp l, act_from_regex r inp l -> supported_actions l.
  Proof.
    intros r SUPP inp l. induction 1; try solve[inversion IHact_from_regex; auto].
    - constructor; constructor. auto.
    - inversion IHact_from_regex. subst x l0.
      inversion H2. subst r0.
      inversion H1. subst r0 r3.
      constructor; auto. constructor. auto.
    - inversion IHact_from_regex. subst x l0.
      inversion H2. subst r0.
      inversion H1. subst r0 r3.
      constructor; auto. constructor. auto.
    - inversion IHact_from_regex. subst x l0.
      inversion H2. subst r0.
      inversion H1. subst r0 r3.
      repeat (constructor; auto).
    - inversion IHact_from_regex. subst x l0.
      inversion H2. subst r0.
      inversion H1. subst greedy0 r0. rewrite <- H5 in *.
      assert (INF: delta = +∞). {
        destruct delta; try discriminate. reflexivity.
      }
      rewrite INF.
      repeat (constructor; auto).
    - inversion IHact_from_regex. subst x l0.
      inversion H2. subst r0. inversion H1. subst gid r0.
      repeat (constructor; auto).
  Qed.

  (** * In a valid list of actions, all checks are ordered (non-strictly) from more to less restrictive. *)

  Definition input_le (inp1 inp2: input): Prop :=
    inp1 = inp2 \/ strict_suffix inp1 inp2 forward.

  Lemma input_le_refl: Relations_1.Reflexive input input_le.
  Proof.
    unfold Relations_1.Reflexive. intro x. left. reflexivity.
  Qed.

  Lemma input_le_trans: Relations_1.Transitive input_le.
  Proof.
    unfold Relations_1.Transitive. intros x y z XY YZ.
    destruct XY as [-> | XY]; destruct YZ as [-> | YZ].
    - apply input_le_refl.
    - right. auto.
    - right. auto.
    - right. eapply strict_suffix_trans; eauto.
  Qed.

  #[global] Add Relation input input_le
    reflexivity proved by input_le_refl
    transitivity proved by input_le_trans
    as input_le_rel.

  Fixpoint actions_checks (act: actions): list input :=
    match act with
    | [] => []
    | Acheck inpcheck :: q => inpcheck :: actions_checks q
    | _ :: q => actions_checks q
    end.
  
  Lemma afr_checks_ordered:
    forall r inp act,
      act_from_regex r inp act -> Sorted input_le (inp :: actions_checks act).
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
    - simpl in *. constructor; auto.
      constructor. reflexivity.
    - simpl in *. inversion IHact_from_regex. subst a l0. constructor; auto.
      destruct actions_checks as [|inpcheck q]; constructor.
      inversion H4. subst b l0. transitivity inp; auto.
      apply advance_input_n_suffix with (n := n). congruence.
  Qed.


  (** * In a valid list of actions, a check is always followed by a quantifier. *)
  Definition checks_fby_quant (act: actions) :=
    forall (i: nat) (inpcheck: input),
      List.nth_error act i = Some (Acheck inpcheck) ->
      exists greedy min delta r,
        List.nth_error act (S i) = Some (Areg (Quantified greedy min delta r)).
  
  Lemma afr_checks_fby_quant:
    forall r inp act, act_from_regex r inp act -> checks_fby_quant act.
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
    - intros i inpcheck EQ_CHECK. destruct i as [ | []]; try discriminate.
      specialize (IHact_from_regex (S n) inpcheck EQ_CHECK). auto.
    - (* Quantifier case: more interesting *)
      (* Either we consider the newly introduced check, in which case this is trivial, or we consider another check, in which case we apply IH *)
      intros i inpcheck EQ_CHECK. destruct i as [|[|[|i]]]; try discriminate; simpl in EQ_CHECK.
      + injection EQ_CHECK as <-.
        exists greedy. exists 0. exists delta. exists r1. reflexivity.
      + specialize (IHact_from_regex (S i) inpcheck EQ_CHECK). auto.
    - (* Apply IH *)
      intros i inpcheck EQ_CHECK. destruct i as [|[|i]]; simpl in EQ_CHECK; try discriminate.
      specialize (IHact_from_regex (S i) inpcheck EQ_CHECK). auto.
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
    | Areg r :: l => regex_size r + chunk_size l
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

  (* Computes the actions fuel after taking the first regex into account, but before arriving to the last chunk. *)
  Fixpoint actions_fuel' (inp: input) (act: actions) {struct act}: nat :=
    match act with
    | Acheck _ :: Areg r :: l => (* r must then be a quantifier *)
      match first_check_input l with
      (* Not last chunk *)
      | Some _ => 2 + actions_fuel' inp l
      (* Last chunk *)
      | None =>
          (* let bonus := if checks_pass then 1 else 0 in
          1 + (bonus + remaining_length inp forward) * last_chunk_size (Areg r :: l) *)
          1
      end
    | Acheck _ :: _ => 0 (* should not happen *)
    | Areg r :: l => regex_size r + actions_fuel' inp l
    | Aclose _ :: l => 1 + actions_fuel' inp l
    | [] => 0 (* should not happen *)
    end.
  
  (* The actual actions fuel, which starts by treating the first regex specially if there are at least two chunks *)
  Definition actions_fuel (inp: input) (act: actions): nat :=
    match first_check_input act with
    (* Only one (last) chunk: bonus is one *)
    | None => (1 + remaining_length inp forward) * chunk_size act
    (* At least two chunks *)
    | Some inpchk =>
        let b := is_strict_suffix inp inpchk forward in
        let beginning_fuel := match act with
        | Areg (Quantified _ _ _ r) :: l =>
          (if b then 1 else 3 + regex_size r) + actions_fuel' inp l
        | _ => actions_fuel' inp act
        end in
        let last := ((if b then 1 else 0) + remaining_length inp forward) * last_chunk_size act in
        beginning_fuel + last
    end.



  (* Invariant: the size of every chunk is less than the size of the next check regex, if any *)
  Lemma chunk_size_lt:
    forall r inp act, act_from_regex r inp act ->
      forall i acttail, acttail = List.skipn i act ->
        forall rchk, next_check_regex acttail = Some rchk ->
          chunk_size acttail < regex_size rchk.
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
        intros rchk EQ_rchk. specialize (IHact_from_regex rchk EQ_rchk). lia.
      + specialize (IHact_from_regex 0 _ eq_refl). subst acttail. simpl in *.
        intros rchk EQ_rchk. specialize (IHact_from_regex rchk EQ_rchk). lia.
      + apply IHact_from_regex with (i := S i). auto.
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
    forall r inp act, act_from_regex r inp act ->
      forall i acttail, acttail = skipn i act ->
        forall inpchk, first_check_input acttail = Some inpchk ->
        chunk_size acttail < last_chunk_size acttail.
  Proof.
    intros r inp act AFR.
    pose proof chunk_size_lt r inp act AFR as CHKSZ_LT.
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
      (*destruct (a is (Acheck _)) eqn:IS_CHECK.
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
      (* Idea: apply CHKSZ_LT to show that regex_size rsub + chunk_size act < regex_size rchk for some rchk, then apply IHact with acttail = the appropriate tail *)
      specialize (CHKSZ_LT 0 (a :: act) eq_refl).
      unfold checks_fby_quant in CHK_FBY_QUANT.
      pose proof (proj1 (first_check_input_nth_error (a :: act) inpchk)) FSTCHK as [i [FSTCHK_NTH1 FSTCHK_NTH2]].
      specialize (CHK_FBY_QUANT _ _ FSTCHK_NTH1). destruct CHK_FBY_QUANT as [greedy [min [delta [rquant CHK_FBY_QUANT]]]].
      specialize (CHKSZ_LT (Quantified greedy min delta rquant)).
      specialize_prove CHKSZ_LT. { eauto using next_check_regex_nth_error. }
      specialize (IHact i _ eq_refl).
      destruct (first_check_input (skipn i act)) as [inpchknext | ] eqn:SNDCHK.
      * specialize (IHact _ eq_refl).
        assert (last_chunk_size (skipn i act) = last_chunk_size act). { 
          pose proof last_chunk_size_skipn (a :: act) i inpchk FSTCHK_NTH1.
          simpl in H. rewrite FSTCHK in H. auto.
        }
        assert (regex_size (Quantified greedy min delta rquant) <= chunk_size (skipn i act)). {
          pose proof nth_error_skipn _ _ _ CHK_FBY_QUANT. simpl in H0.
          rewrite H0. simpl. lia.
        }
        simpl in *. lia.
      * assert (last_chunk_size act = chunk_size (skipn i act)). {
          pose proof last_chunk_size_skipn_last (a :: act) i inpchk FSTCHK_NTH1 SNDCHK.
          simpl in H. rewrite FSTCHK in H. auto.
        }
        assert (regex_size (Quantified greedy min delta rquant) <= chunk_size (skipn i act)). {
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
    forall r inp act,
      act_from_regex r inp act ->
      last_chunk_size act <= regex_size r.
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
      + simpl. rewrite FSTCHK. auto.
      + simpl. rewrite FSTCHK. lia.
    - simpl in IHact_from_regex. destruct (first_check_input l) eqn:FSTCHK.
      + auto.
      + rewrite last_chunk_size_nocheck by assumption. lia.
    - simpl in *. destruct (first_check_input l); assumption.
    - simpl in IHact_from_regex. destruct (first_check_input l) eqn:FSTCHK.
      + auto.
      + rewrite last_chunk_size_nocheck by assumption. lia.
    - simpl in *. destruct (first_check_input l); lia.
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
    | Areg r :: l => regex_size r + actions_size l
    end.
  
  Fixpoint sum_to_n (n_min_i: nat) (n: nat) {struct n_min_i} :=
    match n_min_i with
    | 0 => n
    | S n_min_i' => (n - n_min_i) + sum_to_n n_min_i' n
    end.
  
  Definition num_checks (act: actions) := length (actions_checks act).

  Lemma chunk_size_bound:
    forall r inp act, act_from_regex r inp act ->
      forall i acttail, acttail = skipn i act ->
        chunk_size acttail <= regex_size r - num_checks acttail.
  Proof.
    induction 1; try solve[intros i acttail EQ_acttail; apply IHact_from_regex with (i := S i); auto].
    - intros i acttail EQ_acttail. destruct i as [|i]; subst acttail; simpl.
      + unfold num_checks. simpl. lia.
      + rewrite skipn_nil. simpl. lia.
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
    - (* Sequence *)
      intros i acttail EQ_acttail. destruct i as [|[|i]]; subst acttail; simpl.
      + specialize (IHact_from_regex 0 (Areg (Sequence r1 r2) :: l) eq_refl). simpl in IHact_from_regex.
        unfold num_checks in *. simpl in *. lia.
      + specialize (IHact_from_regex 0 (Areg (Sequence r1 r2) :: l) eq_refl). simpl in IHact_from_regex.
        unfold num_checks in *. simpl in *. lia.
      + apply IHact_from_regex with (i := S i). auto.
    - (* Quantifier iteration *)
      intros i acttail EQ_acttail. destruct i as [|[|[|i]]]; simpl in *.
      + subst acttail. specialize (IHact_from_regex 0 (Areg (Quantified greedy 0 (NoI.N 1 + delta)%NoI r1) :: l) eq_refl).
        simpl in IHact_from_regex. simpl. unfold num_checks in *. simpl in *. lia.
      + subst acttail. specialize (IHact_from_regex 0 (Areg (Quantified greedy 0 (NoI.N 1 + delta)%NoI r1) :: l) eq_refl).
        simpl in IHact_from_regex. simpl. unfold num_checks in *. simpl in *. lia.
      + subst acttail. specialize (IHact_from_regex 0 (Areg (Quantified greedy 0 (NoI.N 1 + delta)%NoI r1) :: l) eq_refl).
        simpl in IHact_from_regex. simpl. unfold num_checks in *. simpl in *. lia.
      + apply IHact_from_regex with (i := S i). auto.
    - (* Group *)
      intros i acttail EQ_acttail. destruct i as [|[|i]]; subst acttail; simpl.
      + specialize (IHact_from_regex 0 (Areg (Group gid r1) :: l) eq_refl).
        unfold num_checks in *. simpl in *. lia.
      + specialize (IHact_from_regex 0 (Areg (Group gid r1) :: l) eq_refl).
        unfold num_checks in *. simpl in *. lia.
      + apply IHact_from_regex with (i := S i). auto.
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
    - destruct (a is (Acheck _)) eqn:IS_CHECK.
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
    forall r inp act, act_from_regex r inp act ->
      forall i acttail, acttail = skipn i act ->
        actions_size acttail <= num_checks acttail + sum_to_n (num_checks acttail) (regex_size r).
  Proof.
    intros r inp act AFR. pose proof chunk_size_bound r inp act AFR as CHK_BOUND.
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
             (* replace (length (actions_checks (Areg r0 :: act))) with (1 + length (actions_checks (skipn (S (chunk_length (Areg r0 :: act))) (Areg r0 :: act)))) by admit. *)
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
             (* replace (length (actions_checks (Areg r0 :: act))) with (1 + length (actions_checks (skipn (S (chunk_length (Areg r0 :: act))) (Areg r0 :: act)))) by admit. *)
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
  Admitted.

  Lemma is_strict_suffix_incr:
    forall inp nextinp inpchk dir,
      advance_input inp dir = Some nextinp ->
      Bool.le (is_strict_suffix inp inpchk dir) (is_strict_suffix nextinp inpchk dir).
  Admitted.

  Lemma is_strict_suffix_incr':
    forall inp n nextinp inpchk dir,
      advance_input_n inp n dir = nextinp ->
      Bool.le (is_strict_suffix inp inpchk dir) (is_strict_suffix nextinp inpchk dir).
  Admitted.

  Lemma actions_fuel'_monotonic_inp:
    forall inp nextinp cont,
      strict_suffix nextinp inp forward ->
      actions_fuel' inp cont >= actions_fuel' nextinp cont.
  Proof.
    intros inp nextinp cont SS. induction cont.
    - simpl. lia.
    - destruct a; simpl; try lia.
      destruct cont as [ | [r | ? | ?] l]; simpl; try lia.
      destruct first_check_input.
      + simpl in IHcont. lia.
      + lia.
  Qed.

  Lemma read_decreases_fuel':
    forall inp cd nextinp cont,
      advance_input inp forward = Some nextinp ->
      actions_fuel' inp (Areg (Regex.Character cd) :: cont) >
      actions_fuel' nextinp cont.
  Proof.
    intros inp cd nextinp cont ADV. simpl.
    induction cont.
    - simpl. lia.
    - simpl. destruct a; simpl; try lia.
      destruct cont as [|[r | ? | ?] l]; simpl; try lia.
      destruct first_check_input.
      + simpl in IHcont. lia.
      + lia.
  Qed.

  (* Similar to read_decreases_fuel' *)
  Lemma read_backref_decreases_fuel':
    forall inp gid n nextinp cont,
      advance_input_n inp n forward = nextinp ->
      actions_fuel' inp (Areg (Backreference gid) :: cont) >
      actions_fuel' nextinp cont.
  Proof.
    intros inp gid n nextinp cont ADV. simpl.
    destruct (Chars.input_eq_dec inp nextinp).
    { rewrite <- e. lia. }
    induction cont.
    - simpl. lia.
    - simpl. destruct a; simpl; try lia.
      destruct cont as [|[r | ? | ?] l]; simpl; try lia.
      destruct first_check_input.
      + simpl in IHcont. lia.
      + lia.
  Qed.

  (* TODO Move to Linden *)
  Lemma remaining_length_current_str:
    forall inp dir, remaining_length inp dir = length (current_str inp dir).
  Proof.
    intros [next pref] []; reflexivity.
  Qed.

  Lemma read_decreases_fuel:
    forall inp cd nextinp cont,
      advance_input inp forward = Some nextinp ->
      actions_fuel inp (Areg (Regex.Character cd) :: cont) > actions_fuel nextinp cont.
  Proof.
    intros inp cd nextinp cont EQ_nextinp.
    unfold actions_fuel. simpl first_check_input.
    destruct first_check_input as [inpchk|] eqn:FSTCHK.
    - simpl actions_fuel'.
      pose proof read_decreases_fuel' inp cd nextinp cont EQ_nextinp.
      simpl in H.
      replace (last_chunk_size (Areg _ :: cont)) with (last_chunk_size cont).
      2: { unfold last_chunk_size at 2. simpl first_check_input.
        rewrite FSTCHK. reflexivity. }
      assert (((if is_strict_suffix inp inpchk forward then 1 else 0) +
remaining_length inp forward) * last_chunk_size cont >= ((if is_strict_suffix nextinp inpchk forward then 1 else 0) +
remaining_length nextinp forward) * last_chunk_size cont). {
        unfold ge.
        apply PeanoNat.Nat.mul_le_mono_r.
        replace (remaining_length inp forward) with (S (remaining_length nextinp forward)).
        2: {
          symmetry. do 2 rewrite remaining_length_current_str. apply advance_current_plus_one. auto.
        }
        pose proof is_strict_suffix_incr inp nextinp inpchk forward EQ_nextinp.
        destruct is_strict_suffix; destruct is_strict_suffix; try discriminate; lia.
      }
      destruct cont as [|[r | ? | ?] l]; simpl in *; try lia.
      destruct r; try lia.
      assert ((if (is_strict_suffix nextinp inpchk forward: bool) then 1 else S (S (S (regex_size r)))) <= regex_size (Quantified greedy min delta r)). {
        simpl. destruct (is_strict_suffix nextinp inpchk forward); lia.
      }
      lia.
    - simpl. unfold gt. apply le_lt_S.
      apply PeanoNat.Nat.add_le_mono_l.
      replace (remaining_length inp forward) with (S (remaining_length nextinp forward)).
      2: {
        symmetry. do 2 rewrite remaining_length_current_str. apply advance_current_plus_one. auto.
      }
      simpl. lia.
  Qed.

  Lemma read_backref_decreases_fuel:
    forall inp gid n nextinp cont,
      advance_input_n inp n forward = nextinp ->
      actions_fuel inp (Areg (Backreference gid) :: cont) > actions_fuel nextinp cont.
  Proof.
    intros inp gid n nextinp cont EQ_nextinp.
    unfold actions_fuel. simpl first_check_input.
    destruct first_check_input as [inpchk|] eqn:FSTCHK.
    - simpl actions_fuel'.
      pose proof read_backref_decreases_fuel' inp gid n nextinp cont EQ_nextinp.
      simpl in H.
      replace (last_chunk_size (Areg _ :: cont)) with (last_chunk_size cont).
      2: { simpl.  rewrite FSTCHK. reflexivity. }
      assert (((if is_strict_suffix inp inpchk forward then 1 else 0) +
remaining_length inp forward) * last_chunk_size cont >= ((if is_strict_suffix nextinp inpchk forward then 1 else 0) +
remaining_length nextinp forward) * last_chunk_size cont). {
        apply PeanoNat.Nat.mul_le_mono_r.
        destruct (Chars.input_eq_dec inp nextinp).
        { rewrite <- e. reflexivity. }
        (*assert (Bool.le (is_strict_suffix inp inpchk forward) (is_strict_suffix nextinp inpchk forward)) by admit. (* Follows from EQ_nextinp *)*)
        pose proof is_strict_suffix_incr' inp n nextinp inpchk forward EQ_nextinp.
        assert (remaining_length nextinp forward < remaining_length inp forward) by admit. (* Follows from n0: inp <> nextinp and EQ_nextinp *)
        destruct is_strict_suffix; destruct is_strict_suffix; try discriminate; lia.
      }
      destruct cont as [|[r | ? | ?] l]; simpl in *; try lia.
      destruct r; try lia.
      assert ((if (is_strict_suffix nextinp inpchk forward: bool) then 1 else S (S (S (regex_size r)))) <= regex_size (Quantified greedy min delta r)). {
        simpl. destruct (is_strict_suffix nextinp inpchk forward); lia.
      }
      lia.
    - simpl. unfold gt. apply le_lt_S.
      apply PeanoNat.Nat.add_le_mono_l.
      assert (remaining_length nextinp forward <= remaining_length inp forward) by admit. (* Follows from EQ_nextinp *)
      apply PeanoNat.Nat.mul_le_mono_nonneg; lia.
  Admitted.

  Lemma actions_fuel_notlast_le:
    forall inp act inpchk,
      first_check_input act = Some inpchk ->
      actions_fuel inp act <=
        actions_fuel' inp act +
        ((if is_strict_suffix inp inpchk forward then 1 else 0) + remaining_length inp forward) * last_chunk_size act.
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
      + (* Done *) discriminate.
      + (* Epsilon *) apply IHfuel.
        { apply afr_pop_epsilon. auto. }
        unfold actions_fuel in FUEL. unfold actions_fuel.
        simpl in FUEL.
        destruct first_check_input as [inpchk|] eqn:FSTCHK.
        * destruct cont as [|[] cont]; try lia.
          destruct r0; try lia.
          simpl in FUEL, FSTCHK. simpl.
          rewrite FSTCHK in FUEL. rewrite FSTCHK.
          destruct is_strict_suffix; lia.
        * lia.
      + (* Read *) destruct read_char as [[c nextinp]|] eqn:READ; try discriminate.
        specialize (IHfuel nextinp cont).
        specialize_prove IHfuel. { apply afr_pop_char with (inp := inp) (cd := cd).
        1: auto. eapply read_char_success_advance; eauto. }
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
              simpl in H. rewrite FSTCHK in FUEL, H. lia.
          }
          assert (IH2: compute_tree rer (Areg r2 :: cont) inp gm forward fuel <> None). {
            apply IHfuel.
            - eapply afr_pop_disj_r; eauto.
            - pose proof actions_fuel_notlast_le inp (Areg r2 :: cont) inpchk.
              specialize (H FSTCHK).
              simpl in H. rewrite FSTCHK in FUEL, H. lia.
          }
          destruct (compute_tree rer (Areg r1 :: cont) inp gm forward fuel); try contradiction.
          destruct compute_tree; try contradiction. discriminate.
        * simpl in FSTCHK.
          assert (IH1: compute_tree rer (Areg r1 :: cont) inp gm forward fuel <> None). {
            apply IHfuel.
            - eapply afr_pop_disj_l; eauto.
            - unfold actions_fuel. simpl first_check_input. rewrite FSTCHK.
              simpl chunk_size in *.
              unfold gt in FUEL. unfold gt.
              assert ((1 + remaining_length inp forward) * (regex_size r1 + chunk_size cont) < (1 + remaining_length inp forward) * S (regex_size r1 + regex_size r2 + chunk_size cont)). {
                apply PeanoNat.Nat.mul_lt_mono_pos_l; lia.
              }
              lia.
          }
          assert (IH2: compute_tree rer (Areg r2 :: cont) inp gm forward fuel <> None). {
            apply IHfuel.
            - eapply afr_pop_disj_r; eauto.
            - unfold actions_fuel. simpl first_check_input. rewrite FSTCHK.
              simpl chunk_size in *.
              unfold gt in FUEL. unfold gt.
              assert ((1 + remaining_length inp forward) * (regex_size r1 + chunk_size cont) < (1 + remaining_length inp forward) * S (regex_size r1 + regex_size r2 + chunk_size cont)). {
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
          simpl in H. simpl first_check_input in FSTCHK. rewrite FSTCHK in FUEL, H. lia.
        * simpl last_chunk_size in FUEL.
          apply IHfuel. 1: apply afr_pop_sequence; auto.
          unfold actions_fuel. setoid_rewrite FSTCHK.
          simpl chunk_size in *.
          unfold gt in FUEL. unfold gt.
          assert ((1 + remaining_length inp forward) * (regex_size r1 + (regex_size r2 + chunk_size cont)) < (1 + remaining_length inp forward) * S (regex_size r1 + regex_size r2 + chunk_size cont)). {
            apply PeanoNat.Nat.mul_lt_mono_pos_l; lia.
          }
          lia.
      + pose proof suppregex_suppactions r SUPP_REGEX inp _ AFR as SUPP_ACTIONS.
        inversion SUPP_ACTIONS. subst x l. inversion H1. subst r0. inversion H0. subst greedy0 min delta r0.
        simpl noi_pred.
        assert (IHiter: compute_tree rer (Areg r1 :: Acheck inp :: Areg (Quantified greedy 0 +∞ r1) :: cont) inp (Groups.GroupMap.reset (def_groups r1) gm) forward fuel <> None). {
          apply IHfuel.
          - apply afr_pop_quant_free_iter. auto.
          - unfold actions_fuel. simpl first_check_input. cbv match.
            replace (is_strict_suffix inp inp forward) with false by admit.
            destruct (match r1 with Quantified _ _ _ _ => true | _ => false end) eqn:R1_QUANT.
            + destruct r1; try discriminate. simpl actions_fuel'.
              unfold actions_fuel in FUEL. simpl first_check_input in FUEL.
              destruct first_check_input as [inpchk | ] eqn:FSTCHK.
              * simpl last_chunk_size in *. rewrite FSTCHK in FUEL. rewrite FSTCHK.
                destruct (is_strict_suffix inp inpchk forward) eqn:SS.
                -- simpl in *.
                   assert (regex_size (Quantified greedy 0 +∞ (Quantified greedy0 min delta r1)) <= last_chunk_size cont). {
                     pose proof chunk_size_lt_last r inp _ AFR 0 _ eq_refl inpchk FSTCHK. simpl in H.
                     rewrite FSTCHK in H. simpl. lia.
                   }
                   simpl in H.
                   lia.
                -- simpl in *. lia.
              * simpl in FUEL. simpl. rewrite FSTCHK. lia.
            + replace (match r1 with | Quantified _ _ _ r0 => _ | _ => _ end) with (actions_fuel' inp (Areg r1 :: Acheck inp :: Areg (Quantified greedy 0 +∞ r1) :: cont)).
              2: { destruct r1; try discriminate; reflexivity. }
              unfold actions_fuel in FUEL. simpl first_check_input in FUEL.
              simpl. destruct first_check_input as [inpchk | ] eqn:FSTCHK.
              * simpl last_chunk_size in *. rewrite FSTCHK in FUEL.
                destruct (is_strict_suffix inp inpchk forward) eqn:SS.
                -- simpl in *.
                   assert (regex_size (Quantified greedy 0 +∞ r1) <= last_chunk_size cont). {
                     pose proof chunk_size_lt_last r inp _ AFR 0 _ eq_refl inpchk FSTCHK. simpl in H.
                     rewrite FSTCHK in H. simpl. lia.
                   }
                   simpl in H.
                   lia.
                -- simpl in *. lia.
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
              simpl last_chunk_size in FUEL. rewrite FSTCHK in FUEL.
              lia.
            + simpl in FUEL. unfold actions_fuel. rewrite FSTCHK. simpl. lia.
        }
        destruct compute_tree; try contradiction.
        destruct compute_tree; try contradiction. discriminate.
      + (* No lookarounds *) exfalso. pose proof suppregex_suppactions r SUPP_REGEX inp _ AFR. inversion H. inversion H2. inversion H5.
      + (* Group *)
        assert (CONT: compute_tree rer (Areg r0 :: Aclose id :: cont) inp (Groups.GroupMap.open (idx inp) id gm) forward fuel <> None). {
          apply IHfuel.
          - apply afr_pop_group. auto.
          - unfold actions_fuel in FUEL. simpl first_check_input in FUEL.
            destruct first_check_input as [inpchk|] eqn:FSTCHK.
            + simpl in FUEL.
              pose proof actions_fuel_notlast_le inp (Areg r0 :: Aclose id :: cont) inpchk FSTCHK.
              simpl in H. rewrite FSTCHK in FUEL, H. lia.
            + unfold actions_fuel. setoid_rewrite FSTCHK.
              unfold gt in *.
              simpl chunk_size in *. lia.
        }
        destruct compute_tree; try contradiction. discriminate.
      + (* Anchor *)
        destruct anchor_satisfied; try discriminate.
        assert (CONT: compute_tree rer cont inp gm forward fuel <> None). {
          apply IHfuel.
          - apply afr_pop_anchor with (a := a). auto.
          - unfold actions_fuel in FUEL. simpl first_check_input in FUEL.
            destruct first_check_input as [inpchk|] eqn:FSTCHK.
            + simpl in FUEL. rewrite FSTCHK in FUEL. pose proof actions_fuel_notlast_le inp cont inpchk FSTCHK. lia.
            + unfold actions_fuel. rewrite FSTCHK. simpl chunk_size in FUEL. lia.
        }
        destruct compute_tree; try contradiction. discriminate.
      + (* Backreference *)
        destruct read_backref as [[br_str nextinp]| ] eqn:READ; try discriminate.
        assert (CONT: compute_tree rer cont nextinp gm forward fuel <> None). {
          apply IHfuel.
          - eapply afr_pop_backref. + eauto. + admit. (* The backreference read succeeds, hence nextinp = advance_input n inp for some n *)
          - assert (exists n: nat, advance_input_n inp n forward = nextinp) by admit.
            destruct H as [n ADV].
            pose proof read_backref_decreases_fuel inp id n nextinp cont ADV.
            lia.
        }
        destruct compute_tree; try contradiction. discriminate.
      + (* Check *)
        destruct is_strict_suffix eqn:SS; try discriminate.
        assert (CONT: compute_tree rer cont inp gm forward fuel <> None). {
          apply IHfuel.
          - apply afr_pop_check with (inpcheck := inpcheck). + apply is_strict_suffix_correct. auto. + auto.
          - unfold actions_fuel in FUEL. simpl first_check_input in FUEL.
            cbv match in FUEL.
            unfold actions_fuel. simpl in FUEL.
            (* AFR implies that cont must start with a quantifier *)
            destruct cont as [|a cont].
            1: exfalso; admit.
            destruct a as [rsub | ? | ?]. 2,3: exfalso; admit.
            destruct rsub. 1-4,6-9: exfalso; admit.
            simpl first_check_input. destruct first_check_input as [inpchknext | ] eqn:SNDCHK.
            + (* NON-TRIVIAL: is_strict_suffix inp inpcheck forward = true implies
              is_strict_suffix inp inpchknext forward = true *)
              replace (is_strict_suffix inp inpchknext forward) with true by admit. rewrite SS in FUEL. lia.
            + rewrite SS in FUEL. simpl in *. rewrite SNDCHK in FUEL. simpl in *. lia. 
        }
        destruct compute_tree; try contradiction. discriminate.
      + assert (CONT: compute_tree rer cont inp (Groups.GroupMap.close (idx inp) gid gm) forward fuel <> None). {
          apply IHfuel.
          - apply afr_pop_close with (gid := gid). auto.
          - unfold actions_fuel in FUEL. simpl first_check_input in FUEL.
            destruct first_check_input as [inpchk|] eqn:FSTCHK.
            + pose proof actions_fuel_notlast_le inp cont inpchk FSTCHK. simpl in FUEL. rewrite FSTCHK in FUEL. lia.
            + unfold actions_fuel. rewrite FSTCHK. simpl in *. lia.
        }
        destruct compute_tree; try contradiction. discriminate.
  Admitted.


End MembershipProof.
