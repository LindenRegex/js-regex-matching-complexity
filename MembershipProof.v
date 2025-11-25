From Linden Require Import Regex Parameters Semantics Chars StrictSuffix.
From Warblre Require Import Base.
Require Import List.
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

  Fixpoint first_check_input (act: actions): option input :=
    match act with
    | [] => None
    | Areg _ :: l | Aclose _ :: l => first_check_input l
    | Acheck inp :: _ => Some inp
    end.

  Fixpoint last_chunk_size (act: actions): nat :=
    match act with
    | Acheck _ :: _ => 0 (* should not happen *)
    | Aclose gid :: l => 1 + last_chunk_size l
    | Areg r :: l => regex_size r + last_chunk_size l
    | [] => 0
    end.

  Fixpoint actions_fuel' (inp: input) (act: actions) (checks_pass: bool) {struct act}: nat :=
    match act with
    | Acheck _ :: Areg r :: l =>
      match first_check_input l with
      (* Not last chunk *)
      | Some _ => 2 + actions_fuel' inp l checks_pass
      (* Last chunk *)
      | None =>
          let bonus := if checks_pass then 1 else 0 in
          1 + (bonus + remaining_length inp forward) * last_chunk_size (Areg r :: l)
      end
    | Acheck _ :: _ => 0 (* should not happen *)
    | Areg r :: l => regex_size r + actions_fuel' inp l checks_pass
    | Aclose _ :: l => 1 + actions_fuel' inp l checks_pass
    | [] => 0 (* should not happen *)
    end.
  
  Definition actions_fuel (inp: input) (act: actions): nat :=
    match first_check_input act with
    (* Only one (last) chunk: bonus is one *)
    | None => (1 + remaining_length inp forward) * last_chunk_size act
    (* At least two chunks *)
    | Some inpchk =>
        let b := is_strict_suffix inp inpchk forward in
        match act with
        | Areg (Quantified _ _ _ r) :: l =>
          (if b then 1 else 3 + regex_size r) + actions_fuel' inp l b
        | _ => actions_fuel' inp act b
        end
    end.


End MembershipProof.
