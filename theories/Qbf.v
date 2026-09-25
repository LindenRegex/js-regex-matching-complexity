From Stdlib Require Import MSetList PeanoNat List.
Open Scope bool_scope.

(** * Definition of quantified boolean formulas and their interpretation. *)

(* A variable is represented by a nat. It is indexed from 1 to numVars. *)
Definition variable: Type := nat.

(* A literal is either a variable or its negation. *)
Inductive literal: Type :=
| PosVar: variable -> literal
| NegVar: variable -> literal.

(* A clause is a disjunction of literals. *)
Definition clause: Type := list literal.

(* Quantifiers: either exists or not exists. *)
Inductive quantifier: Type :=
| Exists
| NotExists.

(* Positive propositional formula in CNF: a list of clauses *)
Definition pos_formula := list clause.

(* Propositional formula in CNF that can be negated *)
Inductive formula: Type :=
| PosForm: pos_formula -> formula
| NegForm: pos_formula -> formula.

(* A QBF (in CNF) is a list of quantifiers followed by a conjunction of clauses. *)
Definition qbf := (list quantifier * formula)%type.

(* The underlying CNF of a QBF *)
Definition inner_pos_formula (f: formula): pos_formula :=
  match f with | PosForm pf | NegForm pf => pf end.

(* Number of clauses in a QBF. *)
Definition num_clauses_formula (f: formula): nat :=
  length (inner_pos_formula f).

Definition num_clauses_qbf (q: qbf): nat :=
  num_clauses_formula (snd q).

Fixpoint num_literals_pos_formula (pf: pos_formula): nat :=
  match pf with
  | nil => 0
  | c::pf => length c + num_literals_pos_formula pf
  end.

Definition num_literals_formula (f: formula): nat :=
  num_literals_pos_formula (inner_pos_formula f).

Definition num_literals_qbf (q: qbf): nat :=
  num_literals_formula (snd q).

Definition var_of_literal (l: literal): variable :=
  match l with PosVar v | NegVar v => v end.

Definition vars_of_pos_formula (pf: pos_formula): list variable :=
  flat_map (map var_of_literal) pf.

Lemma length_vars_of_pos_formula pf:
  length (vars_of_pos_formula pf) = num_literals_pos_formula pf.
Proof. induction pf as [|c pf IH]; cbn; rewrite ?length_app, ?length_map; auto. Qed.

Definition qbf_size (q: qbf): nat :=
  (* [1 +] allows a formula like [c * qbf_size q] to absorb the encoding's constant part. *)
  1 + length (fst q) + num_clauses_qbf q + num_literals_qbf q.

Definition pos_formula_size (pf: pos_formula): nat :=
  1 + length pf + num_literals_pos_formula pf.

(* A QBF is well-formed if all the variables that appear in it are quantified. *)
Definition wf_var (num_vars: nat) (v: variable): Prop := v <> 0 /\ v <= num_vars.

Inductive wf_literal (num_vars: nat): literal -> Prop :=
| WfPosVar: forall v, wf_var num_vars v -> wf_literal num_vars (PosVar v)
| WfNegVar: forall v, wf_var num_vars v -> wf_literal num_vars (NegVar v).

Definition wf_clause (num_vars: nat) (c: clause): Prop :=
  Forall (wf_literal num_vars) c.

Definition wf_pos_formula (num_vars: nat) (pf: pos_formula) :=
  Forall (wf_clause num_vars) pf.

Lemma wf_vars_of_pos_formula num_vars pf:
  wf_pos_formula num_vars pf ->
  forall v, In v (vars_of_pos_formula pf) -> wf_var num_vars v.
Proof.
  unfold wf_pos_formula, wf_clause; do 2 setoid_rewrite Forall_forall.
  intros WF v (c & INc & (l & <- & INl)%in_map_iff)%in_flat_map; now destruct (WF c INc l INl).
Qed.

Definition uses_all_vars (num_vars: nat) (pf: pos_formula): Prop :=
  forall v, wf_var num_vars v -> In v (vars_of_pos_formula pf).

Lemma uses_all_vars_num_literals num_vars pf:
  uses_all_vars num_vars pf -> num_vars <= num_literals_pos_formula pf.
Proof.
  intro USES; rewrite <- length_vars_of_pos_formula, <- (length_seq num_vars 1).
  apply NoDup_incl_length; [apply seq_NoDup|].
  intros v (LO & HI)%in_seq; apply USES.
  split; [apply Nat.neq_0_lt_0, LO | apply Nat.lt_succ_r, HI].
Qed.

Lemma uses_all_vars_num_vars_le num_vars num_vars' pf:
  wf_pos_formula num_vars pf -> uses_all_vars num_vars' pf -> num_vars' <= num_vars.
Proof.
  intros WF USES; destruct num_vars' as [|nv]; [apply Nat.le_0_l|].
  apply (wf_vars_of_pos_formula _ _ WF), USES; now split.
Qed.

Inductive wf_formula (num_vars: nat): formula -> Prop :=
| WfPosForm: forall pf, wf_pos_formula num_vars pf -> wf_formula num_vars (PosForm pf)
| WfNegForm: forall pf, wf_pos_formula num_vars pf -> wf_formula num_vars (NegForm pf).

Inductive wf_qbf: qbf -> Prop :=
| Wf: forall (ql: list quantifier) (f: formula),
  wf_formula (length ql) f ->
  wf_qbf (ql, f).

(** ** Environments *)
(* An environment is a set of variables that are true *)
Module Environment := MSetList.Make Nat.
Definition env := Environment.t.

(** ** Functional version of validity of QBF *)
Definition true_variable (e: env) (v: variable): bool :=
  Environment.mem v e.

Definition true_literal (e: env) (l: literal): bool :=
  match l with
  | PosVar v => true_variable e v
  | NegVar v => negb (true_variable e v)
  end.

Definition true_clause (e: env) (c: clause): bool :=
  List.existsb (true_literal e) c.

Definition true_pos_formula (e: env) (pf: pos_formula): bool :=
  List.forallb (true_clause e) pf.

Definition true_formula (e: env) (f: formula): bool :=
  match f with
  | PosForm pf => true_pos_formula e pf
  | NegForm pf => negb (true_pos_formula e pf)
  end.

(* n is the variable to be assigned at this stage *)
(* ql contains the remaining quantifiers to process, including the nth one *)
Fixpoint qbf_true_aux (e: env) (n: nat) (ql: list quantifier) (f: formula) {struct ql}: bool :=
  match ql with
  | nil => true_formula e f
  | quant::q =>
    match quant with
    | Exists =>
        qbf_true_aux (Environment.add n e) (S n) q f ||
        qbf_true_aux e (S n) q f
    | NotExists =>
        negb (qbf_true_aux (Environment.add n e) (S n) q f) &&
        negb (qbf_true_aux e (S n) q f)
    end
  end.

Definition qbf_true (q: qbf): bool :=
  qbf_true_aux Environment.empty 1 (fst q) (snd q).

