From JsRegexOptp Require Import GroupMaps Qbf.
From Linden Require Import Parameters Groups.

Section GroupMapQbfEquiv.
  Context {params: LindenParameters}.

  Definition equiv_gm_env (gm: group_map) (e: env) :=
    forall i, gm_satisfies_var gm i = true_variable e i.

  Lemma equiv_gm_env_lit:
    forall gm e, equiv_gm_env gm e ->
      forall l: literal, gm_satisfies_lit gm l = true_literal e l.
  Proof.
    intros gm e EQUIV l. unfold gm_satisfies_lit, true_literal.
    destruct l; rewrite EQUIV; reflexivity.
  Qed.

  Lemma equiv_gm_env_clause:
    forall gm e, equiv_gm_env gm e ->
      forall c: clause, gm_satisfies_clause gm c = true_clause e c.
  Proof.
    intros gm e EQUIV c. unfold gm_satisfies_clause, true_clause.
    induction c.
    - reflexivity.
    - simpl. rewrite equiv_gm_env_lit with (e := e), IHc; auto.
  Qed.

  Lemma equiv_gm_env_conjunct:
    forall gm e, equiv_gm_env gm e ->
      forall pf: pos_formula, gm_satisfies_conjunct gm pf = true_pos_formula e pf.
  Proof.
    intros gm e EQUIV pf. unfold gm_satisfies_conjunct. induction pf.
    - reflexivity.
    - simpl. rewrite equiv_gm_env_clause with (e := e), IHpf; auto.
  Qed.

  Lemma equiv_gm_env_formula:
    forall gm e, equiv_gm_env gm e ->
      forall f: formula, gm_satisfies_formula gm f = true_formula e f.
  Proof.
    intros gm e EQUIV f. destruct f as [pf|pf]; simpl; [|f_equal]; apply equiv_gm_env_conjunct; auto.
  Qed.


  Lemma environment_mem_add_eq:
    forall (e: env) (n: nat), Environment.mem n (Environment.add n e) = true.
  Proof.
    intros e n. apply Environment.mem_spec, Environment.add_spec. left. reflexivity.
  Qed.

  Lemma environment_mem_add_neq:
    forall (e: env) (n m: nat), n <> m -> Environment.mem n (Environment.add m e) = Environment.mem n e.
  Proof.
    intros e n m NEQ. apply Bool.eq_iff_eq_true.
    do 2 rewrite Environment.mem_spec. rewrite Environment.add_spec. tauto.
  Qed.

  Lemma equiv_gm_env_add:
    forall gm e, equiv_gm_env gm e ->
      forall n range, equiv_gm_env (GroupMap.add n range gm) (Environment.add n e).
  Proof.
    intros gm e EQUIV n range i.
    unfold gm_satisfies_var, true_variable, GroupMap.find, GroupMap.add.
    destruct (PeanoNat.Nat.eq_dec i n).
    - subst i.
      rewrite GroupMap.Facts.add_eq_o by auto.
      rewrite environment_mem_add_eq. reflexivity.
    - rewrite GroupMap.Facts.add_neq_o by auto. rewrite environment_mem_add_neq by auto.
      apply EQUIV.
  Qed.

  Theorem equiv_gm_env_aux:
    forall gm e, equiv_gm_env gm e ->
      forall n ql f, gm_satisfies_qbf_aux gm n ql f = qbf_true_aux e n ql f.
  Proof.
    intros gm e EQUIV n ql f. revert gm e EQUIV n. induction ql as [|qt ql IH].
    - simpl. intros gm e EQUIV _. apply equiv_gm_env_formula. auto.
    - intros gm e EQUIV n. simpl. destruct qt.
      + rewrite IH with (gm := gm) (e := e) (n := S n); auto.
        rewrite IH with (gm := GroupMap.add n _ gm) (e := Environment.add n e) (n := S n).
        2: apply equiv_gm_env_add; auto.
        apply Bool.orb_comm.
      + rewrite IH with (gm := gm) (e := e) (n := S n); auto.
        rewrite IH with (gm := GroupMap.add n _ gm) (e := Environment.add n e) (n := S n).
        2: apply equiv_gm_env_add; auto.
        apply Bool.andb_comm.
  Qed.

  Lemma empty_equiv:
    equiv_gm_env GroupMap.empty Environment.empty.
  Proof.
    intro i. reflexivity.
  Qed.

  Corollary equiv_gm_env_true:
    forall q: qbf, gm_satisfies_qbf_aux GroupMap.empty 1 (fst q) (snd q) = qbf_true q.
  Proof.
    intro q. unfold qbf_true. apply equiv_gm_env_aux. apply empty_equiv.
  Qed.
End GroupMapQbfEquiv.