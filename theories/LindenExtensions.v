(* TODO: Upstream in Linden. *)

From Linden Require Import Regex Parameters Semantics Chars StrictSuffix Tree Groups
  FunctionalSemantics FunctionalUtils GroupMapLemmas EquivLemmas Equivalence FlatMap.
From Linden.Rewriting Require Import ProofSetup.
From Warblre Require Import Base spec.RegExpRecord Notations.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations.

Lemma FlatMap_pair {X Y: Type} (f: X -> list Y -> Prop) (a b: X) l la lb:
    FlatMap.determ f -> FlatMap.FlatMap [a; b] f l -> f a la -> f b lb -> l = la ++ lb.
Proof.
  intros DET FM ? ?; inversion FM; subst; inversion FM0; subst; inversion FM1; subst.
  rewrite app_nil_r; f_equal; eapply DET; eauto.
Qed.

Lemma list_sum_repeat (k n: nat): list_sum (repeat k n) = n * k.
Proof. induction n; simpl; congruence. Qed.

Lemma concat_repeat_len {A: Type} (l: list A) n:
  length (concat (repeat l n)) = length l * n.
Proof. now rewrite length_concat, map_repeat, list_sum_repeat, Nat.mul_comm. Qed.

Lemma rev_concat_repeat {A: Type} (l: list A) i:
  rev (concat (repeat l i)) = concat (repeat (rev l) i).
Proof.
  induction i as [|i IH]; [reflexivity|].
  replace (S i) with (i + 1) at 1 by lia.
  rewrite repeat_app, concat_app, rev_app_distr; simpl; rewrite app_nil_r; congruence.
Qed.

Lemma skipn_concat_repeat {A: Type} (l: list A) n i:
  skipn (i * length l) (concat (repeat l n)) = concat (repeat l (n - i)).
Proof.
  induction i as [|i IH]; [now rewrite Nat.sub_0_r|].
  destruct (Nat.lt_decidable i n).
  - replace (n - i) with (S (n - S i)) in IH by lia. simpl in *.
    now rewrite <- skipn_skipn, IH, skipn_app, skipn_all, Nat.sub_diag.
  - replace (n - S i) with 0 by lia. simpl. apply skipn_all2.
    rewrite concat_repeat_len, (Nat.mul_comm (length l) n).
    change (length l + i * length l) with ((S i) * length l).
    apply Nat.mul_le_mono_r. lia.
Qed.

Lemma skipn_head {A: Type}:
  forall (l: list A) (a: A) (i: nat), i < length l ->
    skipn i l = nth i l a :: skipn (S i) l.
Proof.
  induction l as [|x l IH]; intros a [|i] LT; cbn in *; try lia; auto; apply IH; lia.
Qed.

Lemma app_nonempty_iff {A: Type}:
  forall l1 l2: list A, l1 ++ l2 <> [] <-> l1 <> [] \/ l2 <> [].
Proof. intros [|] [|]; cbn; intuition discriminate. Qed.

Lemma FlatMap_empty_iff {X Y: Type} (lx: list X) (f: X -> list Y -> Prop) (ly: list Y):
    FlatMap.determ f -> FlatMap.FlatMap lx f ly ->
    (ly <> [] <-> exists (x: X) (fx: list Y), In x lx /\ f x fx /\ fx <> []).
Proof.
  intros DET FM; split.
  - destruct ly as [|y ly]; [easy|intros _].
    destruct (FlatMap.In_FlatMap _ _ _ y DET FM (or_introl eq_refl))
      as (x & fx & INx & Fx & INy).
    exists x, fx. now destruct fx.
  - intros (x & fx & INx & Fx & NE).
    pose proof FlatMap.FlatMap_in _ _ _ _ _ DET FM INx Fx as ALL.
    destruct fx as [|y fx]; [easy|]. inversion ALL; subst. now destruct ly.
Qed.

Section LindenExtensions.
  Context {params: LindenParameters}.

  Inductive all_suffixes (P: actions -> Prop): actions -> Prop :=
  | as_nil: P [] -> all_suffixes P []
  | as_cons: forall a l, P (a :: l) -> all_suffixes P l -> all_suffixes P (a :: l).

  Lemma all_suffixes_hd: forall {P l}, all_suffixes P l -> P l.
  Proof. now destruct 1. Qed.

  Lemma all_suffixes_tl: forall {P a l}, all_suffixes P (a :: l) -> all_suffixes P l.
  Proof. now inversion 1. Qed.

  Lemma triangle_even n: n * S n = 2 * Nat.div2 (n * S n).
  Proof.
    assert (exists q, n * S n = 2 * q) as [q ->]
      by (induction n as [|n [q ?]]; [exists 0 | exists (q + S n)]; nia).
    now rewrite Nat.div2_double.
  Qed.

  (* The start positions ECMAScript's [exec] tries in turn. *)
  Lemma advance_input_samestr inp nextinp dir:
      advance_input inp dir = Some nextinp ->
      input_str nextinp = input_str inp.
  Proof.
    destruct inp as [next pref], dir; [destruct next | destruct pref];
      inversion 1; simpl; now rewrite <- app_assoc.
  Qed.

  Lemma strict_suffix_samestr:
    forall inp' inp dir, strict_suffix inp' inp dir -> input_str inp' = input_str inp.
  Proof. induction 1; apply advance_input_samestr in H; congruence. Qed.

  Lemma remaining_le_full_length inp dir:
    remaining_length inp dir <= length (input_str inp).
  Proof. destruct inp, dir; simpl; rewrite length_app, length_rev; lia. Qed.

  Lemma strict_suffix_remaining inp' inp dir:
      strict_suffix inp' inp dir -> remaining_length inp' dir < remaining_length inp dir.
  Proof. destruct inp', inp, dir; simpl; now apply strict_suffix_current. Qed.

  Lemma is_strict_suffix_irrefl inp dir: is_strict_suffix inp inp dir = false.
  Proof.
    destruct is_strict_suffix eqn:SS; [|reflexivity].
    now apply is_strict_suffix_correct, ss_irreflexive in SS.
  Qed.

  Definition matches_at (rer: RegExpRecord) (r: regex) (inp: input): Prop :=
    forall t, is_tree rer [Areg r] inp GroupMap.empty forward t -> first_leaf t inp <> None.

  Lemma matches_at_tree {rer r inp t}:
      is_tree rer [Areg r] inp GroupMap.empty forward t ->
      (matches_at rer r inp <-> first_leaf t inp <> None).
  Proof.
    intro T; split;
      [intro M; exact (M t T)
      |intros NE t' T'; now replace t' with t by eauto using is_tree_determ].
  Qed.

  Lemma matches_at_compute_tr {rer r inp}:
      matches_at rer r inp <->
      first_leaf (compute_tr rer [Areg r] inp GroupMap.empty forward) inp <> None.
  Proof. apply matches_at_tree, compute_tr_is_tree. Qed.

End LindenExtensions.
