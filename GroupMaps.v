From Linden Require Import Groups Parameters.
From JsRegexOptp Require Import Qbf.
Require Import List.

Section GroupMaps.
  Context {params: LindenParameters}.
  Context (q: qbf).

  Let n := length (fst q).

  Definition wf_gm (gm: group_map): Prop :=
    forall gid, gid <= n -> GroupMap.find gid gm = None \/
      GroupMap.find gid gm = Some (GroupMap.Range (2*(gid-1)) (Some (2*(gid-1)+1))).
  
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
  
  Definition gm_satisfies_conjunct (gm: group_map) (cl: list clause): bool :=
    List.forallb (gm_satisfies_clause gm) cl.
  
  Fixpoint gm_satisfies_qbf_aux (gm: group_map) (n: nat) (ql: list quantifier)
    (cl: list clause) {struct ql}: bool :=
    match ql with
    | nil => gm_satisfies_conjunct gm cl
    | Qbf.Exists::ql =>
        gm_satisfies_qbf_aux gm (S n) ql cl ||
        gm_satisfies_qbf_aux (GroupMap.add n (GroupMap.Range (2*(n-1)) (Some (2*(n-1)+1))) gm) (S n) ql cl
    | Qbf.NotExists::ql =>
        negb (gm_satisfies_qbf_aux gm (S n) ql cl) &&
        negb (gm_satisfies_qbf_aux (GroupMap.add n (GroupMap.Range (2*(n-1)) (Some (2*(n-1)+1))) gm) (S n) ql cl)
    end.

End GroupMaps.