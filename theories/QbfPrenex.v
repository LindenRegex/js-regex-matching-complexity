From Stdlib Require Import List Lia.
From JSRegexComplexity Require Import Qbf.
Import ListNotations.
Open Scope bool_scope.

(** * Standard prenex CNF QBF (∃/∀) and reduction to QBF' (∃/¬∃) *)

Inductive pquantifier: Type :=
| PForall
| PExists.

Definition pqbf := (list pquantifier * pos_formula)%type.

(* [n] is the variable quantified at this depth. *)
Fixpoint pqbf_true_aux (e: env) (n: nat) (ql: list pquantifier) (pf: pos_formula)
  {struct ql}: bool :=
  match ql with
  | nil => true_pos_formula e pf
  | quant::ql =>
    match quant with
    | PForall =>
        pqbf_true_aux (Environment.add n e) (S n) ql pf &&
        pqbf_true_aux e (S n) ql pf
    | PExists =>
        pqbf_true_aux (Environment.add n e) (S n) ql pf ||
        pqbf_true_aux e (S n) ql pf
    end
  end.

Definition pqbf_true (pq: pqbf): bool :=
  pqbf_true_aux Environment.empty 1 (fst pq) (snd pq).

Inductive wf_pqbf: pqbf -> Prop :=
| WfP: forall (ql: list pquantifier) (pf: pos_formula),
  wf_pos_formula (length ql) pf ->
  wf_pqbf (ql, pf).

Definition pqbf_size (pq: pqbf): nat :=
  1 + length (fst pq) + length (snd pq) + num_literals_pos_formula (snd pq).

Definition is_forall (q: pquantifier): bool :=
  match q with PForall => true | PExists => false end.

Fixpoint tr_quants (b: bool) (ql: list pquantifier): list quantifier :=
  match ql with
  | nil => nil
  | q::ql => (if xorb b (is_forall q) then NotExists else Exists) :: tr_quants (is_forall q) ql
  end.

Fixpoint tr_body (b: bool) (ql: list pquantifier) (pf: pos_formula): formula :=
  match ql with
  | nil => if b then NegForm pf else PosForm pf
  | q::ql => tr_body (is_forall q) ql pf
  end.

Definition qbf_of_pqbf (pq: pqbf): qbf :=
  (tr_quants false (fst pq), tr_body false (fst pq) (snd pq)).

Section Translation.
  Context (pf: pos_formula).

  Lemma tr_quants_length ql: forall b, length (tr_quants b ql) = length ql.
  Proof. induction ql as [|q ql IH]; intro b; cbn; [reflexivity | now rewrite IH]. Qed.

  Lemma tr_body_last ql:
    forall q b, tr_body b (ql ++ [q]) pf = if is_forall q then NegForm pf else PosForm pf.
  Proof. induction ql as [|q' ql IH]; intros q b; cbn; auto. Qed.

  Lemma tr_body_inner ql: forall b, inner_pos_formula (tr_body b ql pf) = pf.
  Proof. induction ql as [|q ql IH]; intros b; cbn; [destruct b|]; auto. Qed.

  Lemma wf_tr_body ql:
    forall b k, wf_pos_formula k pf -> wf_formula k (tr_body b ql pf).
  Proof. induction ql as [|q ql IH]; intros [] k H; cbn; auto using WfPosForm, WfNegForm. Qed.

  Lemma tr_true_aux ql:
    forall b e n,
      qbf_true_aux e n (tr_quants b ql) (tr_body b ql pf) =
      xorb b (pqbf_true_aux e n ql pf).
  Proof.
    induction ql as [|q ql IH]; intros b e n; [now destruct b|].
    destruct q, b; cbn; rewrite !IH; now destruct pqbf_true_aux, pqbf_true_aux.
  Qed.
End Translation.

Theorem qbf_of_pqbf_true pq: qbf_true (qbf_of_pqbf pq) = pqbf_true pq.
Proof. destruct pq as [ql pf]; apply (tr_true_aux pf ql false). Qed.

Theorem wf_qbf_of_pqbf pq: wf_pqbf pq -> wf_qbf (qbf_of_pqbf pq).
Proof. inversion 1; constructor; rewrite tr_quants_length; auto using wf_tr_body. Qed.

Theorem qbf_size_of_pqbf pq: qbf_size (qbf_of_pqbf pq) = pqbf_size pq.
Proof.
  destruct pq as [ql pf]; unfold qbf_size, pqbf_size, qbf_of_pqbf, num_clauses_qbf,
    num_clauses_formula, num_literals_qbf, num_literals_formula; cbn [fst snd];
    now rewrite tr_quants_length, tr_body_inner.
Qed.

Theorem pcnf_reduces_to_qbf pq:
    wf_pqbf pq ->
    wf_qbf (qbf_of_pqbf pq) /\
    qbf_size (qbf_of_pqbf pq) = pqbf_size pq /\
    qbf_true (qbf_of_pqbf pq) = pqbf_true pq.
Proof. intro WF; auto using wf_qbf_of_pqbf, qbf_size_of_pqbf, qbf_of_pqbf_true. Qed.

Definition ex_forall_exists: pqbf :=
  ([PForall; PExists], [[PosVar 1; PosVar 2]; [NegVar 1; NegVar 2]]).

Lemma wf_ex_forall_exists: wf_pqbf ex_forall_exists.
Proof. repeat constructor; cbn; lia. Qed.

Example ex_forall_exists_translation:
  qbf_of_pqbf ex_forall_exists =
    ([NotExists; NotExists], PosForm [[PosVar 1; PosVar 2]; [NegVar 1; NegVar 2]]).
Proof. now vm_compute. Qed.

Example ex_forall_exists_true:
  pqbf_true ex_forall_exists = true /\ qbf_true (qbf_of_pqbf ex_forall_exists) = true.
Proof. now vm_compute. Qed.

Example ex_forall_exists_size:
  pqbf_size ex_forall_exists = 9 /\ qbf_size (qbf_of_pqbf ex_forall_exists) = 9.
Proof. now vm_compute. Qed.

Example ex_forall_exists_reduction:
  wf_qbf (qbf_of_pqbf ex_forall_exists) /\
  qbf_size (qbf_of_pqbf ex_forall_exists) = pqbf_size ex_forall_exists /\
  qbf_true (qbf_of_pqbf ex_forall_exists) = pqbf_true ex_forall_exists.
Proof. auto using pcnf_reduces_to_qbf, wf_ex_forall_exists. Qed.

Definition ex_forall: pqbf := ([PForall], [[PosVar 1]]).

Example ex_forall_translation:
  qbf_of_pqbf ex_forall = ([NotExists], NegForm [[PosVar 1]]).
Proof. now vm_compute. Qed.

Example ex_forall_false:
  pqbf_true ex_forall = false /\ qbf_true (qbf_of_pqbf ex_forall) = false.
Proof. now vm_compute. Qed.
