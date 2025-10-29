From Coq Require Import MSetList PeanoNat List.
Open Scope bool_scope.

(** * Definition of quantified boolean formulas and their interpretation. *)

(* A variable is represented by a nat. *)
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

(* A QBF (in CNF) is a list of quantifiers followed by a conjunction of clauses. *)
Definition qbf := (list quantifier * list clause)%type.

(* A QBF is well-formed if all the variables that appear in it are quantified. *)
Definition wf_var (num_vars: nat) (v: variable): Prop := v < num_vars.

Inductive wf_literal (num_vars: nat): literal -> Prop :=
| WfPosVar: forall v, wf_var num_vars v -> wf_literal num_vars (PosVar v)
| WfNegVar: forall v, wf_var num_vars v -> wf_literal num_vars (NegVar v).

Definition wf_clause (num_vars: nat) (c: clause): Prop :=
  Forall (wf_literal num_vars) c.

Inductive wf_qbf: qbf -> Prop :=
| Wf: forall (ql: list quantifier) (cl: list clause),
  Forall (wf_clause (length ql)) cl ->
  wf_qbf (ql, cl).

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
| Valid_Exists: forall (n: nat) (e: env) (ql: list quantifier) (cl: list clause),
    qbf_valid (S n) e (ql, cl) ->
    qbf_valid (S n) (Environment.add n e) (ql, cl) ->
    qbf_valid n e (Exists::ql, cl)
| Valid_NotExists: forall (n: nat) (e: env) (ql: list quantifier) (cl: list clause),
    ~qbf_valid (S n) e (ql, cl) ->
    ~qbf_valid (S n) (Environment.add n e) (ql, cl) ->
    qbf_valid n e (NotExists::ql, cl).*)

(** ** Functional version of validity if QBF *)
Definition true_variable (e: env) (v: variable): bool :=
  Environment.mem v e.

Definition valid_literal (e: env) (l: literal): bool :=
  match l with
  | PosVar v => true_variable e v
  | NegVar v => negb (true_variable e v)
  end.

Definition valid_clause (e: env) (c: clause): bool :=
  List.existsb (valid_literal e) c.

(* n is the variable to be assigned at this stage *)
(* ql contains the remaining quantifiers to process, including the nth one *)
Fixpoint qbf_valid_aux (e: env) (n: nat) (ql: list quantifier) (cl: list clause) {struct ql}: bool :=
  match ql with
  | nil => List.forallb (valid_clause e) cl
  | quant::q =>
    match quant with
    | Exists =>
        qbf_valid_aux (Environment.add n e) (S n) q cl ||
        qbf_valid_aux e (S n) q cl
    | NotExists =>
        negb (qbf_valid_aux (Environment.add n e) (S n) q cl) &&
        negb (qbf_valid_aux e (S n) q cl)
    end
  end.

Definition qbf_valid (q: qbf): bool :=
  qbf_valid_aux Environment.empty 0 (fst q) (snd q).

