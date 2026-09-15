(** * QBF encodings but written in Warblre instead of Linden *)

From JsRegexOptp Require Import Qbf RegexEncoding HardnessProofs WarblreExtensions.
From JsRegexOptp Require Import Basics.
From JsRegexOptp Require RegexEncodingPoslk.
From Linden Require Import LWParameters Chars RegexpTranslation EquivMain.
From Warblre Require Import Patterns Numeric Parameters StaticSemantics Result.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations.

(* Linden is imported after us, so its own [regex_size] would win here. *)
Local Notation expanded_size := Basics.expanded_size.

Section WarblreRegexEncoding.
  Context {params: LindenParameters}.
  Context (q: qbf).

  Context (a_char semicolon_char: Parameters.Character).

  Notation nvar := (length (fst q)).

  Definition nat_to_positive (n: nat): positive_integer := BinPos.Pos.of_nat n.

  (* <(a)|a>;.  No variable index: Warblre numbers capturing groups by position. *)
  Definition def_var_regex_w: Patterns.Regex :=
    Patterns.Seq
      (Patterns.Disjunction
        (Patterns.Group None (Patterns.Char a_char))
        (Patterns.Char a_char))
      (Patterns.Char semicolon_char).

  Definition WBackref (n: nat): Patterns.Regex :=
    Patterns.AtomEsc (Patterns.DecimalEsc (nat_to_positive n)).

  Definition check_literal_regex_w (l: literal): Patterns.Regex :=
    match l with
    | PosVar v => WBackref v
    | NegVar v => Patterns.Seq (WBackref v) (Patterns.Char a_char)
    end.

  Fixpoint check_clause_regex_aux_w (c: clause): Patterns.Regex :=
    match c with
    | nil => Patterns.Empty
    | l::q => Patterns.Disjunction (check_literal_regex_w l) (check_clause_regex_aux_w q)
    end.

  Definition check_clause_regex_w (c: clause): Patterns.Regex :=
    Patterns.Seq (check_clause_regex_aux_w c) (Patterns.Char semicolon_char).

  Fixpoint check_conjunct_regex_w (rev_cl: list clause): Patterns.Regex :=
    match rev_cl with
    | nil => Patterns.Empty
    | c::cl => Patterns.Seq (check_conjunct_regex_w cl) (check_clause_regex_w c)
    end.

  Definition check_formula_regex_w (f: formula): Patterns.Regex :=
    match f with
    | PosForm pf => check_conjunct_regex_w (rev pf)
    | NegForm pf => Patterns.NegativeLookahead (check_conjunct_regex_w (rev pf))
    end.

  Fixpoint theRegex_w_aux (ql: list quantifier): Patterns.Regex :=
    match ql with
    | nil => check_formula_regex_w (snd q)
    | Qbf.Exists::ql => Patterns.Seq def_var_regex_w (theRegex_w_aux ql)
    | Qbf.NotExists::ql => Patterns.NegativeLookahead (Patterns.Seq def_var_regex_w (theRegex_w_aux ql))
    end.

  Definition theRegex_w := theRegex_w_aux (fst q).

  Lemma check_clause_aux_size: forall c,
      pattern_expanded_size (check_clause_regex_aux_w c) <= 1 + 4 * length c.
  Proof. induction c as [|l c IH]; cbn; [|destruct l; cbn]; lia. Qed.

  Lemma check_conjunct_size: forall cl,
      pattern_expanded_size (check_conjunct_regex_w cl)
      <= 1 + 4 * length cl + 4 * num_literals_pos_formula cl.
  Proof. induction cl as [|c cl IH]; cbn; [|pose proof check_clause_aux_size c; cbn]; lia. Qed.

  Lemma check_formula_size: forall f,
      pattern_expanded_size (check_formula_regex_w f)
      <= 2 + 4 * num_clauses_formula f + 4 * num_literals_formula f.
  Proof.
    intros [pf|pf]; unfold num_clauses_formula, num_literals_formula; cbn;
      pose proof check_conjunct_size (rev pf); rewrite num_literals_pos_formula_rev, length_rev in *; lia.
  Qed.

  Lemma theRegex_w_aux_size: forall ql,
      pattern_expanded_size (theRegex_w_aux ql)
      <= 9 * length ql + pattern_expanded_size (check_formula_regex_w (snd q)).
  Proof. induction ql as [|[|] ql IH]; cbn; lia. Qed.

  Theorem theRegex_w_size: pattern_expanded_size theRegex_w <= 9 * qbf_size q.
  Proof.
    unfold theRegex_w, qbf_size, num_clauses_qbf, num_literals_qbf.
    pose proof theRegex_w_aux_size (fst q); pose proof check_formula_size (snd q); lia.
  Qed.

  (* [n] is the number of capturing groups before [wr]. *)
  Definition enc (nb n k: nat) (wr: Patterns.Regex) (lr: regex): Prop :=
    StaticSemantics.countLeftCapturingParensWithin_impl wr = k /\
    num_groups lr = k /\
    simple_regex nb wr /\
    forall nm, warblre_to_linden wr n nm = Success lr.

  Local Ltac enc_cbn :=
    cbn [StaticSemantics.countLeftCapturingParensWithin_impl num_groups
         simple_regex simple_quantifier warblre_to_linden wquantpref_to_linden
         atomesc_to_linden Result.bind Nat.add def_var_regex_w def_var_regex].

  Local Ltac enc_leaf := unfold enc; repeat split; intros; reflexivity.

  Lemma enc_empty nb n: enc nb n 0 Patterns.Empty Epsilon.
  Proof. enc_leaf. Qed.

  Lemma enc_char nb n c: enc nb n 0 (Patterns.Char c) (Regex.Character (CdSingle c)).
  Proof. enc_leaf. Qed.

  Lemma enc_inputend nb n: enc nb n 0 Patterns.InputEnd (Anchor EndInput).
  Proof. enc_leaf. Qed.

  Lemma enc_backref nb n v: wf_var nb v -> enc nb n 0 (WBackref v) (Backreference v).
  Proof.
    intros [NZ LE]; unfold enc, WBackref; enc_cbn; unfold positive_to_nat, nat_to_positive;
      rewrite Pnat.Nat2Pos.id by exact NZ; repeat split; auto.
  Qed.

  Local Ltac enc_bin :=
    intros (CA & GA & SA & TA) (CB & GB & SB & TB);
    unfold enc; enc_cbn; rewrite CA, CB, GA, GB; repeat split; auto;
    intro nm; rewrite TA; enc_cbn; rewrite GA; enc_cbn; now rewrite TB.

  Lemma enc_seq nb n j k a la b lb:
      enc nb n j a la -> enc nb (j + n) k b lb ->
      enc nb n (j + k) (Patterns.Seq a b) (Sequence la lb).
  Proof. enc_bin. Qed.

  Lemma enc_disj nb n j k a la b lb:
      enc nb n j a la -> enc nb (j + n) k b lb ->
      enc nb n (j + k) (Patterns.Disjunction a b) (Disjunction la lb).
  Proof. enc_bin. Qed.

  Lemma enc_seq0 nb n a la b lb:
      enc nb n 0 a la -> enc nb n 0 b lb -> enc nb n 0 (Patterns.Seq a b) (Sequence la lb).
  Proof. intros; now apply (enc_seq nb n 0 0). Qed.

  Lemma enc_disj0 nb n a la b lb:
      enc nb n 0 a la -> enc nb n 0 b lb ->
      enc nb n 0 (Patterns.Disjunction a b) (Disjunction la lb).
  Proof. intros; now apply (enc_disj nb n 0 0). Qed.

  Local Ltac enc_wrap :=
    intros (C & G & SI & T); unfold enc; enc_cbn; rewrite ?C, ?G; repeat split; auto;
    intro nm; now rewrite T.

  Lemma enc_neglook nb n k a la:
      enc nb n k a la -> enc nb n k (Patterns.NegativeLookahead a) (Lookaround NegLookAhead la).
  Proof. enc_wrap. Qed.

  Lemma enc_look nb n k a la:
      enc nb n k a la -> enc nb n k (Patterns.Lookahead a) (Lookaround LookAhead la).
  Proof. enc_wrap. Qed.

  Lemma enc_star nb n k a la:
      enc nb n k a la ->
      enc nb n k (Patterns.Quantified a (Patterns.Greedy Patterns.Star))
                 (Quantified true 0 +∞ la).
  Proof. enc_wrap. Qed.

  Lemma enc_group nb n k a la:
      enc nb (S n) k a la ->
      enc nb n (S k) (Patterns.Group None a) (Group (S n) la).
  Proof. enc_wrap. Qed.

  Lemma enc_defvar nb n k r lr:
      enc nb (S n) k r lr ->
      enc nb n (S k) (Patterns.Seq def_var_regex_w r)
                  (Sequence (def_var_regex a_char semicolon_char (S n)) lr).
  Proof. enc_wrap. Qed.

  Local Hint Resolve enc_empty enc_char enc_inputend enc_backref
    enc_seq0 enc_disj0 enc_neglook enc_look : core.

  Local Ltac enc_form :=
    cbn [check_literal_regex_w check_literal_regex
         check_clause_regex_aux_w check_clause_regex_aux
         check_clause_regex_w check_clause_regex
         check_conjunct_regex_w check_conjunct_regex
         check_formula_regex_w check_formula_regex].

  Section Forms.
    Context (nb: nat).
    Hypothesis NB: nvar <= nb.

    Lemma wf_var_nb v: wf_var nvar v -> wf_var nb v.
    Proof. intros []; split; lia. Qed.

    Lemma check_literal_enc l n:
        wf_literal nvar l ->
        enc nb n 0 (check_literal_regex_w l) (check_literal_regex a_char l).
    Proof. inversion 1; enc_form; auto using wf_var_nb. Qed.

    Lemma check_clause_aux_enc c:
      forall n, wf_clause nvar c ->
        enc nb n 0 (check_clause_regex_aux_w c) (check_clause_regex_aux a_char c).
    Proof. induction c; intro n; inversion 1; enc_form; auto using check_literal_enc. Qed.

    Lemma check_clause_enc c n:
        wf_clause nvar c ->
        enc nb n 0 (check_clause_regex_w c) (check_clause_regex a_char semicolon_char c).
    Proof. intro; enc_form; eauto using enc_seq0, check_clause_aux_enc. Qed.

    Lemma check_conjunct_enc cl:
      forall n, Forall (wf_clause nvar) cl ->
        enc nb n 0 (check_conjunct_regex_w cl) (check_conjunct_regex a_char semicolon_char cl).
    Proof. induction cl; intro n; inversion 1; enc_form; auto using check_clause_enc. Qed.

    Lemma check_formula_enc f n:
        wf_formula nvar f ->
        enc nb n 0 (check_formula_regex_w f) (check_formula_regex a_char semicolon_char f).
    Proof. inversion 1; enc_form; auto using check_conjunct_enc, Forall_rev. Qed.
  End Forms.

  Section WellFormed.
    Hypothesis WF: wf_qbf q.

    Lemma wf_snd: wf_formula nvar (snd q).
    Proof. inversion WF; assumption. Qed.

    Lemma theRegex_w_aux_enc:
      forall ql n,
        enc nvar n (length ql) (theRegex_w_aux ql) (theRegex_aux q a_char semicolon_char (S n) ql).
    Proof.
      induction ql as [|[] ql IH]; intro n; cbn [theRegex_w_aux theRegex_aux length];
        auto using check_formula_enc, wf_snd, enc_defvar, enc_neglook.
    Qed.

    Lemma theRegex_w_enc: enc nvar 0 nvar theRegex_w (theRegex q a_char semicolon_char).
    Proof. apply theRegex_w_aux_enc. Qed.

    Lemma theRegex_w_ngroups:
      StaticSemantics.countLeftCapturingParensWithin theRegex_w nil = nvar.
    Proof. apply theRegex_w_enc. Qed.

    Lemma regex_encoding_wl:
      warblre_to_linden theRegex_w 0 (buildnm theRegex_w) =
        Success (theRegex q a_char semicolon_char).
    Proof. apply theRegex_w_enc. Qed.

    Lemma regex_encoding_w_earlyErrors:
      StaticSemantics.earlyErrors theRegex_w [] = Success false.
    Proof. apply simple_earlyErrors; rewrite theRegex_w_ngroups; apply theRegex_w_enc. Qed.
  End WellFormed.

  Context (z_char: Parameters.Character).

  Definition a_semicolon_star_w: Patterns.Regex :=
    Patterns.Quantified (Patterns.Seq (Patterns.Char a_char) (Patterns.Char semicolon_char))
      (Patterns.Greedy Patterns.Star).

  Definition capture_z_regex_w: Patterns.Regex :=
    Patterns.Seq a_semicolon_star_w (Patterns.Group None (Patterns.Char z_char)).

  Definition check_z_regex_w (z: nat): Patterns.Regex :=
    Patterns.Seq (Patterns.Seq a_semicolon_star_w (WBackref z)) Patterns.InputEnd.

  Definition negation_regex_w (rsub: Patterns.Regex) (z: nat): Patterns.Regex :=
    Patterns.Seq (Patterns.Lookahead (Patterns.Disjunction rsub capture_z_regex_w))
                 (check_z_regex_w z).

  Definition check_formula_regex_poslk_w: Patterns.Regex :=
    let conj := check_conjunct_regex_w (rev (inner_pos_formula (snd q))) in
    match snd q with
    | PosForm _ => conj
    | NegForm _ => negation_regex_w conj (S nvar)
    end.

  Fixpoint theRegex_poslk_w_aux (ql: list quantifier): Patterns.Regex :=
    match ql with
    | nil => check_formula_regex_poslk_w
    | Qbf.Exists::ql => Patterns.Seq def_var_regex_w (theRegex_poslk_w_aux ql)
    | Qbf.NotExists::ql' =>
        negation_regex_w (Patterns.Seq def_var_regex_w (theRegex_poslk_w_aux ql'))
                         (RegexEncodingPoslk.z_gid_at q (Qbf.NotExists::ql'))
    end.

  Definition theRegex_poslk_w := theRegex_poslk_w_aux (fst q).

  Lemma negation_regex_w_size rsub z:
      pattern_expanded_size (negation_regex_w rsub z) = 23 + pattern_expanded_size rsub.
  Proof.
    unfold negation_regex_w, check_z_regex_w, capture_z_regex_w,
      a_semicolon_star_w, WBackref; cbn [pattern_expanded_size quantifier_min quantprefix_min]; lia.
  Qed.

  Lemma check_formula_poslk_size:
    pattern_expanded_size check_formula_regex_poslk_w
    <= 24 + 4 * num_clauses_qbf q + 4 * num_literals_qbf q.
  Proof.
    unfold check_formula_regex_poslk_w; measure_unfold; cbv zeta.
    destruct (snd q) as [pf|pf]; pose proof check_conjunct_size (rev pf);
      rewrite num_literals_pos_formula_rev, length_rev in *; cbn [inner_pos_formula];
      rewrite ?negation_regex_w_size; lia.
  Qed.

  Lemma theRegex_poslk_w_aux_size: forall ql,
      pattern_expanded_size (theRegex_poslk_w_aux ql)
      <= 31 * length ql + pattern_expanded_size check_formula_regex_poslk_w.
  Proof.
    induction ql as [|[|] ql IH]; cbn [theRegex_poslk_w_aux length];
      rewrite ?negation_regex_w_size; unfold def_var_regex_w; cbn [pattern_expanded_size]; lia.
  Qed.

  Theorem theRegex_poslk_w_size: pattern_expanded_size theRegex_poslk_w <= 31 * qbf_size q.
  Proof.
    unfold theRegex_poslk_w, qbf_size.
    pose proof theRegex_poslk_w_aux_size (fst q); pose proof check_formula_poslk_size; lia.
  Qed.

  Definition ngroups_form: nat := match snd q with PosForm _ => 0 | NegForm _ => 1 end.

  Fixpoint ngroups_poslk (ql: list quantifier): nat :=
    match ql with
    | nil => ngroups_form
    | Qbf.Exists::ql => S (ngroups_poslk ql)
    | Qbf.NotExists::ql => S (S (ngroups_poslk ql))
    end.

  Lemma ngroups_poslk_closed:
    forall ql, ngroups_poslk ql = length ql + RegexEncodingPoslk.num_notexists ql + ngroups_form.
  Proof. induction ql as [|[] ql IH]; cbn; lia. Qed.

  Notation NB := (ngroups_poslk (fst q)).

  Local Ltac enc_poslk :=
    cbn [RegexEncodingPoslk.a_semicolon_star RegexEncodingPoslk.capture_z_regex
         RegexEncodingPoslk.check_z_regex RegexEncodingPoslk.negation_regex
         a_semicolon_star_w capture_z_regex_w check_z_regex_w negation_regex_w].

  Lemma enc_astar nb n:
      enc nb n 0 a_semicolon_star_w (RegexEncodingPoslk.a_semicolon_star a_char semicolon_char).
  Proof. enc_poslk; apply enc_star, enc_seq0; auto. Qed.

  Lemma enc_capture_z nb n:
      enc nb n 1 capture_z_regex_w
        (RegexEncodingPoslk.capture_z_regex a_char semicolon_char z_char (S n)).
  Proof. apply (enc_seq nb n 0 1); auto using enc_astar, enc_group. Qed.

  Lemma enc_check_z nb n z: wf_var nb z ->
      enc nb n 0 (check_z_regex_w z) (RegexEncodingPoslk.check_z_regex a_char semicolon_char z).
  Proof. intro; unfold check_z_regex_w, RegexEncodingPoslk.check_z_regex; auto using enc_astar. Qed.

  Lemma enc_negation nb n k a la:
      wf_var nb (S (k + n)) -> enc nb n k a la ->
      enc nb n (S k) (negation_regex_w a (S (k + n)))
        (RegexEncodingPoslk.negation_regex a_char semicolon_char z_char la (S (k + n))).
  Proof.
    intros ? ENC; enc_poslk; replace (S k) with (k + 1 + 0) by lia.
    apply enc_seq; auto using enc_disj, enc_capture_z, enc_check_z.
  Qed.

  Section WellFormedPoslk.
    Hypothesis WF: wf_qbf q.

    Local Hint Unfold wf_var : core.
    Local Hint Extern 1 (_ <= _) => lia : core.
    Local Hint Extern 1 (@eq nat _ _) => lia : core.

    Lemma nvar_le_NB: nvar <= NB.
    Proof. rewrite ngroups_poslk_closed; lia. Qed.

    Lemma NB_negform pf: snd q = NegForm pf -> S nvar <= NB.
    Proof. intro E; rewrite ngroups_poslk_closed; unfold ngroups_form; rewrite E; lia. Qed.

    Lemma enc_check_formula_poslk:
      enc NB nvar ngroups_form check_formula_regex_poslk_w
        (RegexEncodingPoslk.check_formula_regex a_char semicolon_char z_char q).
    Proof.
      pose proof nvar_le_NB; pose proof wf_snd WF as W.
      assert (CJ: forall m, enc NB m 0 (check_conjunct_regex_w (rev (inner_pos_formula (snd q))))
                     (check_conjunct_regex a_char semicolon_char (rev (inner_pos_formula (snd q)))))
        by (inversion W; auto using check_conjunct_enc, Forall_rev).
      unfold check_formula_regex_poslk_w, ngroups_form, RegexEncodingPoslk.check_formula_regex;
        cbv zeta; destruct (snd q) eqn:E; [apply CJ|].
      eauto using enc_negation, NB_negform.
    Qed.

    Lemma theRegex_poslk_w_aux_enc:
      forall ql n,
        n + length ql = nvar ->
        RegexEncodingPoslk.num_notexists ql <= RegexEncodingPoslk.num_notexists (fst q) ->
        enc NB n (ngroups_poslk ql) (theRegex_poslk_w_aux ql)
          (RegexEncodingPoslk.theRegex_aux a_char semicolon_char z_char q (S n) ql).
    Proof.
      induction ql as [|[] ql IH]; intros n LEN NE;
        cbn [theRegex_poslk_w_aux RegexEncodingPoslk.theRegex_aux ngroups_poslk length
             RegexEncodingPoslk.num_notexists] in *.
      - replace n with nvar by lia; apply enc_check_formula_poslk.
      - eauto using enc_defvar.
      - pose proof ngroups_poslk_closed ql; pose proof ngroups_poslk_closed (fst q).
        assert (Z: RegexEncodingPoslk.z_gid_at q (Qbf.NotExists::ql) = S (S (ngroups_poslk ql) + n))
          by (unfold RegexEncodingPoslk.z_gid_at, ngroups_form in *; destruct (snd q); cbn; lia).
        rewrite Z; eauto 8 using enc_negation, enc_defvar.
    Qed.

    Theorem theRegex_poslk_w_enc:
      enc NB 0 NB theRegex_poslk_w
        (RegexEncodingPoslk.theRegex a_char semicolon_char z_char q).
    Proof. apply theRegex_poslk_w_aux_enc; lia. Qed.

    Lemma theRegex_poslk_w_ngroups:
      StaticSemantics.countLeftCapturingParensWithin theRegex_poslk_w nil = NB.
    Proof. apply theRegex_poslk_w_enc. Qed.

    Lemma regex_encoding_poslk_wl:
      warblre_to_linden theRegex_poslk_w 0 (buildnm theRegex_poslk_w) =
        Success (RegexEncodingPoslk.theRegex a_char semicolon_char z_char q).
    Proof. apply theRegex_poslk_w_enc. Qed.

    Lemma regex_encoding_poslk_w_earlyErrors:
      StaticSemantics.earlyErrors theRegex_poslk_w [] = Success false.
    Proof.
      apply simple_earlyErrors; rewrite theRegex_poslk_w_ngroups; apply theRegex_poslk_w_enc.
    Qed.
  End WellFormedPoslk.

End WarblreRegexEncoding.

Section Size.
  Context {params: LindenParameters}.
  Context (a_char semicolon_char z_char: Parameters.Character).

  Theorem theString_size q:
    length (theString q a_char semicolon_char z_char) <= 2 * qbf_size q.
  Proof. unfold qbf_size; pose proof str_len q a_char semicolon_char z_char; lia. Qed.

  Theorem reduction_size_linear q:
      expanded_size (RegexEncoding.theRegex q a_char semicolon_char) <= 9 * qbf_size q /\
      expanded_size (RegexEncodingPoslk.theRegex a_char semicolon_char z_char q) <=
        31 * qbf_size q /\
      length (theString q a_char semicolon_char z_char) <= 2 * qbf_size q.
  Proof.
    repeat split;
      auto using theRegex_size, RegexEncodingPoslk.theRegex_poslk_size, theString_size.
  Qed.

End Size.
