From Stdlib Require Import Classes.RelationClasses Lists.List.
From Ltac2 Require Import Ltac2 FMap Constr Printf List Fresh.
Import ListNotations.

(* A complete solver for StrictOrder relations *)
(* solves by finding paths between edges of a graph induced *)
(* by the relation assertions from hypotheses. *)
(* Additionally proves contradictions by finding cycles. *)

(* Finds an item and returns its index *)
Ltac2 rec findi (f : 'a -> bool) (xs : 'a list) : int option :=
  let rec aux f xs i :=
    match xs with
    | [] => None
    | x :: xs =>
      if f x then Some i else aux f xs (Int.add i 1)
    end in
  aux f xs 0.

(* turns a term into some normalized string representation *)
Ltac2 rec term_to_string (t: constr): string :=
  let msg := fprintf "%t" (eval cbv in $t) in
  Message.to_string msg.


Ltac2 rec apply_first (tacs: (unit -> 'a) list): 'a :=
  match tacs with
  | [] => Control.zero (Tactic_failure (Some (fprintf "No tactic succeeded")))
  | tac :: rest =>
    Control.plus tac (fun _ => apply_first rest)
  end.

(* constructs a term that is the transitive path between two elements *)
(* the parameter is a list of hypothesis identifiers *)
Ltac2 rec mk_trans (hyp_list: ident list): constr :=
  match hyp_list with
  | [] => Control.throw (Tactic_failure (Some (fprintf "No hypotheses to apply for transitivity")))
  | [h] => Control.hyp h
  | h :: rest =>
    let h_constr := Control.hyp h in
    let rest_constr := mk_trans rest in
    Control.plus
      (fun _ => constr:(transitivity $h_constr $rest_constr))
      (fun _ =>
        Control.throw (Tactic_failure (Some (
          fprintf "Failed to compose a transitive step. Does your relation implement %t?" open_constr:(Transitive)))))
  end.

(* tries to interpret `h` as `rel a b` and returns a string representation of `a` and `b` *)
Ltac2 get_elements (h: constr) (rel: constr): (string * string) option :=
  match! h with
  | ?r ?a ?b =>
      if Constr.equal r rel then
        Some (term_to_string a, term_to_string b)
      else None
  | _ => None
  end.

(* tried to normalize a term into the form `rel a b` for some a and b *)
Ltac2 normalize (h: constr) (rel: constr): constr option :=
  Control.plus
    (fun _ =>
      let a := open_constr:(_) in
      let b := open_constr:(_) in
      let rel_ab := open_constr:($rel $a $b) in
      let rel_ab_nf := eval cbv in $rel_ab in
      let h_nf := eval cbv in $h in
      Std.unify rel_ab_nf h_nf;
      Some constr:($rel $a $b))
    (fun _ => None).

(* rewrite all hypotheses and the goal using `normalize` *)
Ltac2 normalize_relations (rel: constr): unit :=
  let goal := Control.goal () in
  (match normalize goal rel with
  | Some h =>
    let cl := {
      Std.on_hyps := Some [];
      Std.on_concl := Std.AllOccurrences
    } in
    Std.change None (fun _ => h) cl
  | None => ()
  end);
  List.iter (fun ((id, _, tp)) =>
    match normalize tp rel with
    | Some h =>
      let cl := {
        Std.on_hyps := Some [(id, Std.AllOccurrences, Std.InHyp)];
        Std.on_concl := Std.NoOccurrences
      } in
      Std.change None (fun _ => h) cl
    | None => ()
    end
  ) (Control.hyps ()).

(* constructs the graph from relations in hypotheses *)
Ltac2 build_graph (rel: constr): (string, (string * ident) list) FMap.t :=
  List.fold_left (fun acc ((id, _, tp)) =>
    match get_elements tp rel with
    | Some (a_str, b_str) =>
      match FMap.find_opt a_str acc with
      | Some existing =>
        FMap.add a_str ((b_str, id) :: existing) acc
      | None =>
        FMap.add a_str [(b_str, id)] acc
      end
    | None => acc
    end
  ) (FMap.empty FSet.Tags.string_tag) (Control.hyps ()).

(* given a proof of a self-loop, proves anything by irreflexivity *)
Ltac2 prove_contradiction self_loop: constr :=
  let proof_false :=
    Control.plus
      (fun _ => constr:(irreflexivity $self_loop))
      (fun _ =>
        Control.throw (Tactic_failure (Some (
          fprintf "Failed to derive a contradiction. Does your relation implement %t?" open_constr:(Irreflexive))))) in
  open_constr:(ltac2:(ltac1:(exfalso); exact $proof_false)).

Ltac2 Type walk_kind := [
  (* proof of path from `a` to `b` where edges and vertices are not repeated *)
  | Path (constr)
  (* proof of cycle from `a` to itself *)
  | Cycle (constr)
].

(* in the graph `hyps_map` tries to find a path from `from` to `to` *)
(* It might instead find a cycle for some `a` *)
Ltac2 find_walk hyps_map from to: walk_kind :=
  let rec dfs visited goal current path :=
    match findi (String.equal current) visited with
    | Some idx =>
      (* we have found a cycle *)
      let cycle_proof := mk_trans (List.rev (List.firstn (Int.add idx 1) path)) in
      Cycle cycle_proof
    | None =>
      let visited := current :: visited in
      match FMap.find_opt current hyps_map with
      | Some lst =>
        let try_path (next, hyp_id) () :=
          if String.equal next goal then
            Path (mk_trans (List.rev (hyp_id :: path)))
          else
            dfs visited goal next (hyp_id :: path) in
        apply_first (List.map try_path lst)
      | None =>
        Control.zero (Tactic_failure (Some (fprintf "No path found from %s to %s" current goal)))
      end
    end in
  dfs [] to from [].

Ltac2 print_full_goal () :=
  let hyps := Control.hyps () in
  List.iter (fun h =>
    match h with
    | (id, body, ty) =>
      (match body with
       | None => printf "%I : %t" id ty
       | Some b => printf "%I := %t : %t" id b ty
       end)
    end
  ) hyps;
  printf "----------------------------------------";
  let g := Control.goal () in
  printf "|- %t" g.

(* tries to find a cycle in the graph that will be a contradiction *)
Ltac2 find_contradiction hyps_map: constr :=
  let try_contra hyps_map name :=
    prove_contradiction (match find_walk hyps_map name name with
    | Path pr => pr
    | Cycle pr => pr
    end) in
  let rec try_contras hyps_map names :=
    match names with
    | name :: rest =>
      Control.plus (fun _=> try_contra hyps_map name) (fun _ => try_contras hyps_map rest)
    | [] =>
      Control.zero (Tactic_failure (Some (fprintf "No contradiction found")))
    end in
  try_contras hyps_map (List.map fst (FMap.bindings hyps_map)).

(* collect all hyps of the rel relation, put them in a map, do a dfs until we find the required one *)
Ltac2 solve_strict_order rel: unit :=
  normalize_relations rel;
  let hyps_map := build_graph rel in
  let refined := match get_elements (Control.goal ()) rel with
  | Some (a_str, b_str) =>
    Control.plus (fun _ =>
      match find_walk hyps_map a_str b_str with
      | Path pr => pr
      | Cycle pr => prove_contradiction pr
      end) (fun _ => find_contradiction hyps_map)
  | _ =>
    find_contradiction hyps_map
  end in
  Control.refine (fun _ => refined).

Ltac2 Notation "strict_order" rel(constr) := solve_strict_order rel.

Ltac strict_order rel :=
  let p := ltac2:(rel |- solve_strict_order (Option.get (Ltac1.to_constr rel))) in
  p rel.
