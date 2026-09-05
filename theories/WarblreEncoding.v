(** * QBF encodings but written in Warblre instead of Linden *)

From JsRegexOptp Require Import Qbf RegexEncoding GroupMaps HardnessProofs WarblreExtensions.
From JsRegexOptp Require Import Basics.
From JsRegexOptp Require RegexEncodingPoslk HardnessPoslk.
From Linden Require Import LWParameters Chars Groups Semantics Tree Tactics
  RegexpTranslation FunctionalSemantics ComputeIsTree Utils FunctionalUtils EquivDef
  ResultTranslation EquivMain.
From Warblre Require Import Patterns Numeric Node NodeProps StaticSemantics Result Base
  EarlyErrors Parameters RegExpRecord Semantics Frontend Notation Errors Typeclasses.
From Stdlib Require Import List Lia PeanoNat ZArith.
Import ListNotations.

Section WarblreRegexEncoding.
  Context {params: LindenParameters}.
  Context (q: qbf).

  Context (x_char semicolon_char: Parameters.Character).

  Notation nvar := (length (fst q)).

  Definition nat_to_positive (n: nat): positive_integer := BinPos.Pos.of_nat n.

  (* <(x)|x>;.  No variable index: Warblre numbers capturing groups by position. *)
  Definition def_var_regex_w: Patterns.Regex :=
    Patterns.Seq
      (Patterns.Disjunction
        (Patterns.Group None (Patterns.Char x_char))
        (Patterns.Char x_char))
      (Patterns.Char semicolon_char).

  Definition WBackref (n: nat): Patterns.Regex :=
    Patterns.AtomEsc (Patterns.DecimalEsc (nat_to_positive n)).

  Definition check_literal_regex_w (l: literal): Patterns.Regex :=
    match l with
    | PosVar v => WBackref v
    | NegVar v => Patterns.Seq (WBackref v) (Patterns.Char x_char)
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

  Definition enc (nb n k: nat) (wr: Patterns.Regex) (lr: regex): Prop :=
    StaticSemantics.countLeftCapturingParensWithin_impl wr = k /\
    num_groups lr = k /\
    simple_regex nb wr /\
    forall nm, warblre_to_linden wr n nm = Success lr.

  Local Ltac enc_cbn :=
    cbn [StaticSemantics.countLeftCapturingParensWithin_impl num_groups
         simple_regex simple_quantifier warblre_to_linden wquantpref_to_linden
         atomesc_to_linden Result.bind Nat.add].

  Lemma enc_empty nb n: enc nb n 0 Patterns.Empty Epsilon.
  Proof. unfold enc; repeat split; intros; reflexivity. Qed.

  Lemma enc_char nb n c: enc nb n 0 (Patterns.Char c) (Regex.Character (CdSingle c)).
  Proof. unfold enc; repeat split; intros; reflexivity. Qed.

  Lemma enc_inputend nb n: enc nb n 0 Patterns.InputEnd (Anchor EndInput).
  Proof. unfold enc; repeat split; intros; reflexivity. Qed.

  Lemma enc_backref nb n v: wf_var nb v -> enc nb n 0 (WBackref v) (Backreference v).
  Proof.
    intros [NZ LE].
    assert (ID: positive_to_nat (nat_to_positive v) = v) by (apply Pnat.Nat2Pos.id, NZ).
    unfold enc, WBackref; enc_cbn; rewrite ID; repeat split; intros; auto.
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
    intros (C & G & SI & T); unfold enc; enc_cbn; repeat split; auto;
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
  Proof.
    intros (C & G & SI & T); unfold enc; enc_cbn; rewrite C, G;
      repeat split; auto; intro nm; now rewrite T.
  Qed.

  Lemma enc_defvar nb n k r lr:
      enc nb (S n) k r lr ->
      enc nb n (S k) (Patterns.Seq def_var_regex_w r)
                  (Sequence (def_var_regex x_char semicolon_char (S n)) lr).
  Proof.
    intros (C & G & SI & T); unfold enc; cbn; rewrite C, G; repeat split; auto.
    intro nm; cbn; now rewrite T.
  Qed.

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
    Proof. intros []; split; [assumption | lia]. Qed.

    Lemma check_literal_enc l n:
        wf_literal nvar l ->
        enc nb n 0 (check_literal_regex_w l) (check_literal_regex x_char l).
    Proof. inversion 1; enc_form; auto using wf_var_nb. Qed.

    Lemma check_clause_aux_enc c:
      forall n, wf_clause nvar c ->
        enc nb n 0 (check_clause_regex_aux_w c) (check_clause_regex_aux x_char c).
    Proof. induction c; intro n; inversion 1; enc_form; auto using check_literal_enc. Qed.

    Lemma check_clause_enc c n:
        wf_clause nvar c ->
        enc nb n 0 (check_clause_regex_w c) (check_clause_regex x_char semicolon_char c).
    Proof. intro; enc_form; apply enc_seq0; auto using check_clause_aux_enc. Qed.

    Lemma check_conjunct_enc cl:
      forall n, Forall (wf_clause nvar) cl ->
        enc nb n 0 (check_conjunct_regex_w cl) (check_conjunct_regex x_char semicolon_char cl).
    Proof. induction cl; intro n; inversion 1; enc_form; auto using check_clause_enc. Qed.

    Lemma check_formula_enc f n:
        wf_formula nvar f ->
        enc nb n 0 (check_formula_regex_w f) (check_formula_regex x_char semicolon_char f).
    Proof. inversion 1; enc_form; auto using check_conjunct_enc, Forall_rev. Qed.
  End Forms.

  Section WellFormed.
    Hypothesis WF: wf_qbf q.

    Lemma wf_snd: wf_formula nvar (snd q).
    Proof. inversion WF; assumption. Qed.

    Lemma theRegex_w_aux_enc:
      forall ql n,
        enc nvar n (length ql) (theRegex_w_aux ql) (theRegex_aux q x_char semicolon_char (S n) ql).
    Proof.
      induction ql as [|[] ql IH]; intro n; cbn [theRegex_w_aux theRegex_aux length].
      - apply check_formula_enc; auto using wf_snd.
      - apply enc_defvar, IH.
      - apply enc_neglook, enc_defvar, IH.
    Qed.

    Lemma theRegex_w_enc: enc nvar 0 nvar theRegex_w (theRegex q x_char semicolon_char).
    Proof. apply theRegex_w_aux_enc. Qed.

    Lemma theRegex_w_ngroups:
      StaticSemantics.countLeftCapturingParensWithin theRegex_w nil = nvar.
    Proof. destruct theRegex_w_enc as (C & _); exact C. Qed.

    Lemma regex_encoding_wl:
      warblre_to_linden theRegex_w 0 (buildnm theRegex_w) =
        Success (theRegex q x_char semicolon_char).
    Proof. destruct theRegex_w_enc as (_ & _ & _ & T); apply T. Qed.

    Lemma regex_encoding_w_earlyErrors:
      StaticSemantics.earlyErrors theRegex_w [] = Success false.
    Proof.
      destruct theRegex_w_enc as (_ & _ & SIMPLE & _).
      apply simple_earlyErrors; rewrite theRegex_w_ngroups; exact SIMPLE.
    Qed.
  End WellFormed.

  Context (n_char: Parameters.Character).

  Definition x_semicolon_star_w: Patterns.Regex :=
    Patterns.Quantified (Patterns.Seq (Patterns.Char x_char) (Patterns.Char semicolon_char))
      (Patterns.Greedy Patterns.Star).

  Definition capture_n_regex_w: Patterns.Regex :=
    Patterns.Seq x_semicolon_star_w (Patterns.Group None (Patterns.Char n_char)).

  Definition check_n_regex_w (z: nat): Patterns.Regex :=
    Patterns.Seq (Patterns.Seq x_semicolon_star_w (WBackref z)) Patterns.InputEnd.

  Definition negation_regex_w (rsub: Patterns.Regex) (z: nat): Patterns.Regex :=
    Patterns.Seq (Patterns.Lookahead (Patterns.Disjunction rsub capture_n_regex_w))
                 (check_n_regex_w z).

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
    cbn [RegexEncodingPoslk.x_semicolon_star RegexEncodingPoslk.capture_n_regex
         RegexEncodingPoslk.check_n_regex RegexEncodingPoslk.negation_regex
         x_semicolon_star_w capture_n_regex_w check_n_regex_w negation_regex_w].

  Lemma enc_xstar nb n:
      enc nb n 0 x_semicolon_star_w (RegexEncodingPoslk.x_semicolon_star x_char semicolon_char).
  Proof. enc_poslk; apply enc_star, enc_seq0; auto. Qed.

  Lemma enc_capture_n nb n:
      enc nb n 1 capture_n_regex_w
        (RegexEncodingPoslk.capture_n_regex x_char semicolon_char n_char (S n)).
  Proof.
    enc_poslk; change 1 with (0 + 1);
      apply enc_seq; [apply enc_xstar | apply enc_group; auto].
  Qed.

  Lemma enc_check_n nb n z: wf_var nb z ->
      enc nb n 0 (check_n_regex_w z) (RegexEncodingPoslk.check_n_regex x_char semicolon_char z).
  Proof.
    intro; enc_poslk; apply enc_seq0;
      [apply enc_seq0; [apply enc_xstar | now apply enc_backref] | apply enc_inputend].
  Qed.

  Lemma enc_negation nb n k a la:
      wf_var nb (S (k + n)) -> enc nb n k a la ->
      enc nb n (S k) (negation_regex_w a (S (k + n)))
        (RegexEncodingPoslk.negation_regex x_char semicolon_char n_char la (S (k + n))).
  Proof.
    intros ? ENC; enc_poslk; replace (S k) with (k + 1 + 0) by lia.
    apply enc_seq; [apply enc_look, enc_disj, enc_capture_n; exact ENC | now apply enc_check_n].
  Qed.

  Section WellFormedPoslk.
    Hypothesis WF: wf_qbf q.

    Lemma nvar_le_NB: nvar <= NB.
    Proof. rewrite ngroups_poslk_closed; lia. Qed.

    Lemma NB_negform pf: snd q = NegForm pf -> S nvar <= NB.
    Proof. intro E; rewrite ngroups_poslk_closed; unfold ngroups_form; rewrite E; lia. Qed.

    Lemma enc_check_formula_poslk:
      enc NB nvar ngroups_form check_formula_regex_poslk_w
        (RegexEncodingPoslk.check_formula_regex x_char semicolon_char n_char q).
    Proof.
      pose proof nvar_le_NB;
        assert (CJ: forall m, enc NB m 0 (check_conjunct_regex_w (rev (inner_pos_formula (snd q))))
                      (check_conjunct_regex x_char semicolon_char (rev (inner_pos_formula (snd q)))))
        by (intro m; apply check_conjunct_enc, Forall_rev;
            pose proof wf_snd WF as W; inversion W; assumption).
      unfold check_formula_regex_poslk_w, ngroups_form, RegexEncodingPoslk.check_formula_regex;
        cbv zeta; destruct (snd q) eqn:E; [apply CJ|].
      apply enc_negation; [|apply CJ]; split; [lia | eapply NB_negform, E].
    Qed.

    Lemma theRegex_poslk_w_aux_enc:
      forall ql n,
        n + length ql = nvar -> RegexEncodingPoslk.num_notexists ql <= RegexEncodingPoslk.num_notexists (fst q) ->
        enc NB n (ngroups_poslk ql) (theRegex_poslk_w_aux ql)
          (RegexEncodingPoslk.theRegex_aux x_char semicolon_char n_char q (S n) ql).
    Proof.
      induction ql as [|[] ql IH]; intros n LEN NE;
        cbn [theRegex_poslk_w_aux RegexEncodingPoslk.theRegex_aux ngroups_poslk length
             RegexEncodingPoslk.num_notexists] in *.
      - replace n with nvar by lia; apply enc_check_formula_poslk.
      - apply enc_defvar, IH; lia.
      - pose proof ngroups_poslk_closed ql as CL; pose proof ngroups_poslk_closed (fst q) as CQ.
        assert (Z: RegexEncodingPoslk.z_gid_at q (Qbf.NotExists::ql) = S (S (ngroups_poslk ql) + n))
          by (unfold RegexEncodingPoslk.z_gid_at, ngroups_form in *; cbn [RegexEncodingPoslk.num_notexists];
              destruct (snd q); lia).
        rewrite Z; apply enc_negation; [split; lia | apply enc_defvar, IH; lia].
    Qed.

    Theorem theRegex_poslk_w_enc:
      enc NB 0 NB theRegex_poslk_w
        (RegexEncodingPoslk.theRegex x_char semicolon_char n_char q).
    Proof. apply theRegex_poslk_w_aux_enc; lia. Qed.

    Lemma theRegex_poslk_w_ngroups:
      StaticSemantics.countLeftCapturingParensWithin theRegex_poslk_w nil = NB.
    Proof. destruct theRegex_poslk_w_enc as (C & _); exact C. Qed.

    Lemma regex_encoding_poslk_wl:
      warblre_to_linden theRegex_poslk_w 0 (buildnm theRegex_poslk_w) =
        Success (RegexEncodingPoslk.theRegex x_char semicolon_char n_char q).
    Proof. destruct theRegex_poslk_w_enc as (_ & _ & _ & T); apply T. Qed.

    Lemma regex_encoding_poslk_w_earlyErrors:
      StaticSemantics.earlyErrors theRegex_poslk_w [] = Success false.
    Proof.
      destruct theRegex_poslk_w_enc as (_ & _ & SIMPLE & _).
      apply simple_earlyErrors; rewrite theRegex_poslk_w_ngroups; exact SIMPLE.
    Qed.
  End WellFormedPoslk.

End WarblreRegexEncoding.
