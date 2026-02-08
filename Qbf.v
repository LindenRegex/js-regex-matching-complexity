From Coq Require Import MSetList PeanoNat List.
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

(* A QBF is well-formed if all the variables that appear in it are quantified. *)
Definition wf_var (num_vars: nat) (v: variable): Prop := v <> 0 /\ v <= num_vars.

Inductive wf_literal (num_vars: nat): literal -> Prop :=
| WfPosVar: forall v, wf_var num_vars v -> wf_literal num_vars (PosVar v)
| WfNegVar: forall v, wf_var num_vars v -> wf_literal num_vars (NegVar v).

Definition wf_clause (num_vars: nat) (c: clause): Prop :=
  Forall (wf_literal num_vars) c.

Definition wf_pos_formula (num_vars: nat) (pf: pos_formula) :=
  Forall (wf_clause num_vars) pf.

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

(** ** Propositional version of validity of QBF *)
(*Definition true_variable (e: env) (v: variable): Prop :=
  Environment.In v e.

Inductive valid_literal (e: env): literal -> Prop :=
| ValidPosVar: forall v, true_variable e v -> valid_literal e (PosVar v)
| ValidNegVar: forall v, ~true_variable e v -> valid_literal e (NegVar v).

Definition valid_clause (e: env) (c: clause): Prop :=
  List.Exists (valid_literal e) c.

Inductive qbf_valid: nat -> env -> qbf -> Prop :=
| Valid_noquant: forall (n: nat) (e: env) (cl: list clause),
    Forall (valid_clause e) cl -> qbf_valid n e (nil, cl)
| Valid_Exists_false: forall (n: nat) (e: env) (ql: list quantifier) (cl: list clause),
    qbf_valid (S n) e (ql, cl) ->
    qbf_valid n e (Exists::ql, cl)
| Valid_Exists_true: forall (n: nat) (e: env) (ql: list quantifier) (cl: list clause),
    qbf_valid (S n) (Environment.add n e) (ql, cl) ->
    qbf_valid n e (Exists::ql, cl)
| Valid_NotExists: forall (n: nat) (e: env) (ql: list quantifier) (cl: list clause),
    ~qbf_valid (S n) e (ql, cl) ->
    ~qbf_valid (S n) (Environment.add n e) (ql, cl) ->
    qbf_valid n e (NotExists::ql, cl).*)

(** ** Functional version of validity if QBF *)
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

