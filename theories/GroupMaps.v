From Linden Require Import Groups.
From JsRegexOptp Require Import Basics Qbf Bits.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations.

Section GroupMaps.
  Context {params: LindenParameters}.
  Context (q: qbf).

  Let n := length (fst q).

  Definition var_range (gid: group_id): GroupMap.range :=
    GroupMap.Range (2*(gid-1)) (Some (2*(gid-1)+1)).

  Definition wf_gm (num_vars: nat) (gm: group_map): Prop :=
    forall gid, gid <= num_vars -> GroupMap.find gid gm = None \/
      GroupMap.find gid gm = Some (var_range gid).
  
  Definition gm_satisfies_var (gm: group_map) (v: variable): bool :=
    match GroupMap.find v gm with
    | Some _ => true
    | None => false
    end.

  Definition gm_satisfies_lit (gm: group_map) (l: literal): bool :=
    match l with
    | PosVar v => gm_satisfies_var gm v
    | NegVar v => negb (gm_satisfies_var gm v)
    end.
  
  Definition gm_satisfies_clause (gm: group_map) (c: clause): bool :=
    List.existsb (gm_satisfies_lit gm) c.
  
  Definition gm_satisfies_conjunct (gm: group_map) (pf: pos_formula): bool :=
    List.forallb (gm_satisfies_clause gm) pf.

  Definition gm_satisfies_formula (gm: group_map) (f: formula): bool :=
    match f with
    | PosForm pf => gm_satisfies_conjunct gm pf
    | NegForm pf => negb (gm_satisfies_conjunct gm pf)
    end.
  
  Fixpoint gm_satisfies_qbf_aux (gm: group_map) (n: nat) (ql: list quantifier)
    (f: formula) {struct ql}: bool :=
    match ql with
    | nil => gm_satisfies_formula gm f
    | Qbf.Exists::ql =>
        gm_satisfies_qbf_aux gm (S n) ql f ||
        gm_satisfies_qbf_aux (GroupMap.add n (var_range n) gm) (S n) ql f
    | Qbf.NotExists::ql =>
        negb (gm_satisfies_qbf_aux gm (S n) ql f) &&
        negb (gm_satisfies_qbf_aux (GroupMap.add n (var_range n) gm) (S n) ql f)
    end.

End GroupMaps.

Lemma find_add_eq: forall i r gm, GroupMap.find i (GroupMap.add i r gm) = Some r.
Proof. intros; now apply GroupMap.Facts.add_eq_o. Qed.

Lemma find_add_neq: forall i j r gm,
    i <> j -> GroupMap.find j (GroupMap.add i r gm) = GroupMap.find j gm.
Proof. intros; now apply GroupMap.Facts.add_neq_o. Qed.

Lemma find_empty: forall i, GroupMap.find i GroupMap.empty = None.
Proof. intros; apply GroupMap.Facts.empty_o. Qed.

Lemma wf_gm_empty: forall nv, wf_gm nv GroupMap.empty.
Proof. intros nv gid _. left. apply find_empty. Qed.

Definition agree_below (i: nat) (gm gm': group_map): Prop :=
  forall j, 1 <= j -> j < i -> GroupMap.find j gm = GroupMap.find j gm'.

Lemma agree_below_refl: forall i gm, agree_below i gm gm.
Proof. intros i gm j _ _. reflexivity. Qed.

Lemma agree_below_one: forall gm gm', agree_below 1 gm gm'.
Proof. intros gm gm' j ? ?. lia. Qed.

Lemma agree_below_sym: forall i gm gm', agree_below i gm gm' -> agree_below i gm' gm.
Proof. intros i gm gm' A j ? ?. symmetry. auto. Qed.

Lemma agree_below_weaken: forall i i' gm gm',
    i' <= i -> agree_below i gm gm' -> agree_below i' gm gm'.
Proof. intros i i' gm gm' LE A j ? ?. apply A; lia. Qed.

Lemma agree_below_S: forall i gm gm',
    agree_below i gm gm' -> GroupMap.find i gm = GroupMap.find i gm' ->
    agree_below (S i) gm gm'.
Proof. intros * A EQ j ? ?; destruct (Nat.eq_dec j i) as [->|]; [assumption | apply A; lia]. Qed.

Definition gm_lex_lt (num_vars: nat) (gm gm': group_map): Prop :=
  exists i, 1 <= i /\ i <= num_vars /\
    GroupMap.find i gm = None /\
    GroupMap.find i gm' = Some (var_range i) /\
    agree_below i gm gm'.

Lemma gm_lex_lt_irrefl: forall nv gm, ~ gm_lex_lt nv gm gm.
Proof. intros nv gm (i & _ & _ & NONE & SOME & _); congruence. Qed.

Lemma gm_lex_lt_trans: forall nv gm1 gm2 gm3,
    gm_lex_lt nv gm1 gm2 -> gm_lex_lt nv gm2 gm3 -> gm_lex_lt nv gm1 gm3.
Proof.
  intros nv gm1 gm2 gm3 (i & ? & ? & N1 & S1 & A1) (j & ? & ? & N2 & S2 & A2).
  destruct (Nat.lt_trichotomy i j) as [? | [<- | ?]]; [exists i | congruence | exists j];
    [rewrite <- A2 by lia | rewrite A1 by lia];
    (repeat split; auto; intros k ? ?; now rewrite A1, A2 by lia).
Qed.

Lemma gm_lex_lt_asym: forall nv gm gm', gm_lex_lt nv gm gm' -> ~ gm_lex_lt nv gm' gm.
Proof. intros nv gm gm' LT LT'. eapply gm_lex_lt_irrefl, gm_lex_lt_trans; eauto. Qed.

Lemma gm_lex_trichotomy_aux: forall k nv gm gm',
    k <= nv -> wf_gm nv gm -> wf_gm nv gm' ->
    agree_below (S k) gm gm' \/ gm_lex_lt nv gm gm' \/ gm_lex_lt nv gm' gm.
Proof.
  induction k as [|k IH]; intros nv gm gm' LE WF WF'; [left; apply agree_below_one|].
  destruct (IH nv gm gm' ltac:(lia) WF WF') as [AGREE | [LT | GT]]; auto.
  destruct (WF (S k) ltac:(lia)) as [E|E], (WF' (S k) ltac:(lia)) as [E'|E'];
    try (left; apply agree_below_S; [assumption | now rewrite E, E']);
    [right; left | right; right]; exists (S k); repeat split; auto using agree_below_sym; lia.
Qed.

Lemma gm_lex_trichotomy: forall nv gm gm',
    wf_gm nv gm -> wf_gm nv gm' ->
    agree_below (S nv) gm gm' \/ gm_lex_lt nv gm gm' \/ gm_lex_lt nv gm' gm.
Proof. intros; eauto using gm_lex_trichotomy_aux. Qed.

(** ** Assignments

    An assignment for variables 1, ..., [nv] is a list of [nv] booleans (bit [k] is
    variable [k+1]). *)

Definition assign_var (b: list bool) (v: variable): bool := nth (v - 1) b false.

Definition assign_lit (b: list bool) (l: literal): bool :=
  match l with
  | PosVar v => assign_var b v
  | NegVar v => negb (assign_var b v)
  end.

Definition assign_clause (b: list bool) (c: clause): bool := existsb (assign_lit b) c.

Definition assign_cnf (b: list bool) (pf: pos_formula): bool := forallb (assign_clause b) pf.

Definition bits_of_gm (num_vars: nat) (gm: group_map): list bool :=
  map (gm_satisfies_var gm) (seq 1 num_vars).

Lemma bits_of_gm_length: forall nv gm, length (bits_of_gm nv gm) = nv.
Proof. intros. unfold bits_of_gm. now rewrite length_map, length_seq. Qed.

Lemma assign_var_of_gm: forall nv gm v,
    1 <= v -> v <= nv -> assign_var (bits_of_gm nv gm) v = gm_satisfies_var gm v.
Proof.
  intros nv gm v ? ?. unfold assign_var.
  rewrite nth_indep with (d' := gm_satisfies_var gm 0) by (rewrite bits_of_gm_length; lia).
  unfold bits_of_gm. rewrite map_nth, seq_nth by lia. f_equal. lia.
Qed.

Lemma assign_cnf_of_gm: forall nv gm pf,
    wf_pos_formula nv pf -> assign_cnf (bits_of_gm nv gm) pf = gm_satisfies_conjunct gm pf.
Proof.
  intros ? ? pf WF; unfold assign_cnf, gm_satisfies_conjunct.
  induction WF as [|c pf WFc _ IH]; cbn; [reflexivity | rewrite IH; f_equal].
  unfold assign_clause, gm_satisfies_clause; induction WFc as [|l c [v []|v []] _ IHc];
    cbn; [reflexivity|..]; now rewrite IHc, assign_var_of_gm by lia.
Qed.

Fixpoint gm_of_bits_from (i: nat) (b: list bool): group_map :=
  match b with
  | [] => GroupMap.empty
  | true :: b' => GroupMap.add i (var_range i) (gm_of_bits_from (S i) b')
  | false :: b' => gm_of_bits_from (S i) b'
  end.

Definition gm_of_bits (b: list bool): group_map := gm_of_bits_from 1 b.

Lemma gm_of_bits_from_spec: forall b i,
    (forall j, j < i -> GroupMap.find j (gm_of_bits_from i b) = None) /\
    (forall j, GroupMap.find j (gm_of_bits_from i b) = None \/
               GroupMap.find j (gm_of_bits_from i b) = Some (var_range j)) /\
    map (gm_satisfies_var (gm_of_bits_from i b)) (seq i (length b)) = b.
Proof.
  induction b as [|[] b IH]; intros i; cbn [gm_of_bits_from length seq map];
    [auto using find_empty|..];
    destruct (IH (S i)) as (LOW & WF & MAP); unfold gm_satisfies_var in *; repeat split.
  - intros j ?; now rewrite find_add_neq, LOW by lia.
  - intros j; destruct (Nat.eq_dec j i) as [->|]; rewrite ?find_add_eq, ?find_add_neq; auto.
  - f_equal; [now rewrite find_add_eq|].
    erewrite map_ext_in; [exact MAP|]; intros j [? ?]%in_seq; now rewrite find_add_neq by lia.
  - intros j ?; apply LOW; lia.
  - exact WF.
  - f_equal; [now rewrite LOW by lia | exact MAP].
Qed.

Lemma bits_of_gm_surj: forall nv b,
    length b = nv -> exists gm, wf_gm nv gm /\ bits_of_gm nv gm = b.
Proof.
  intros nv b <-. destruct (gm_of_bits_from_spec b 1) as (_ & WF & MAP).
  exists (gm_of_bits b). split; [intros gid _; apply WF | exact MAP].
Qed.

Lemma agree_below_bits: forall nv gm gm',
    agree_below (S nv) gm gm' -> bits_of_gm nv gm = bits_of_gm nv gm'.
Proof.
  intros * A; unfold bits_of_gm; apply map_ext_in.
  intros j [? ?]%in_seq; unfold gm_satisfies_var; now rewrite A by lia.
Qed.

Lemma gm_lex_lt_bits: forall nv gm gm',
    gm_lex_lt nv gm gm' -> bits_le (bits_of_gm nv gm) (bits_of_gm nv gm') = true.
Proof.
  intros nv gm gm' (i & ? & ? & NONE & SOME & A).
  apply bits_le_map_seq with (i := i); try lia; unfold gm_satisfies_var;
    [now rewrite NONE | now rewrite SOME | intros j ? ?; now rewrite A by lia].
Qed.

Definition is_lex_max_sat (num_vars: nat) (pf: pos_formula) (b: list bool): Prop :=
  length b = num_vars /\ assign_cnf b pf = true /\
  (forall b', length b' = num_vars -> assign_cnf b' pf = true -> bits_le b' b = true).

Lemma is_lex_max_sat_unique: forall nv pf b b',
    is_lex_max_sat nv pf b -> is_lex_max_sat nv pf b' -> b = b'.
Proof. intros * (? & ? & M) (? & ? & M'); auto using bits_le_antisym. Qed.
