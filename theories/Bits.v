(** * Bit strings ordered lexicographically *)

From Stdlib Require Import List Lia PeanoNat.
Import ListNotations.

Fixpoint bits_le (b1 b2: list bool): bool :=
  match b1, b2 with
  | [], _ => true
  | _ :: _, [] => false
  | false :: q1, false :: q2 => bits_le q1 q2
  | false :: _, true :: _ => true
  | true :: _, false :: _ => false
  | true :: q1, true :: q2 => bits_le q1 q2
  end.

Lemma bits_le_refl b: bits_le b b = true.
Proof. induction b as [|[] b IH]; simpl; auto. Qed.

Lemma bits_le_antisym b1:
  forall b2, bits_le b1 b2 = true -> bits_le b2 b1 = true -> b1 = b2.
Proof.
  induction b1 as [|[] b1 IH]; intros [|[] b2] LE1 LE2; cbn in *;
    try discriminate; f_equal; auto.
Qed.

Lemma bits_le_trans b1:
  forall b2 b3, bits_le b1 b2 = true -> bits_le b2 b3 = true -> bits_le b1 b3 = true.
Proof.
  induction b1 as [|[] b1 IH]; intros [|[] b2] [|[] b3] LE1 LE2; cbn in *;
    try discriminate; eauto.
Qed.

Lemma bits_le_total b1: forall b2, bits_le b1 b2 = true \/ bits_le b2 b1 = true.
Proof. induction b1 as [|[] b1 IH]; intros [|[] b2]; cbn; auto. Qed.

Lemma bits_le_zeros n: forall b, length b = n -> bits_le (repeat false n) b = true.
Proof.
  induction n as [|n IH]; intros [|[] b] LEN; cbn in *;
    try discriminate; try reflexivity; apply IH; lia.
Qed.

Lemma bits_le_map_seq nv:
  forall start (f g: nat -> bool) i,
    start <= i -> i < start + nv -> f i = false -> g i = true ->
    (forall j, start <= j -> j < i -> f j = g j) ->
    bits_le (map f (seq start nv)) (map g (seq start nv)) = true.
Proof.
  induction nv as [|nv IH]; intros start f g i LO HI Fi Gi AGREE; simpl; [lia|].
  destruct (Nat.eq_dec start i) as [<-|NE]; [now rewrite Fi, Gi|].
  rewrite (AGREE start) by lia.
  destruct (g start); simpl; apply IH with (i := i); try lia; auto.
  all: intros j ? ?; apply AGREE; lia.
Qed.

Lemma bits_le_complement b1:
  forall b2, length b1 = length b2 ->
    bits_le (map negb b1) (map negb b2) = bits_le b2 b1.
Proof. induction b1 as [|[] b1 IH]; intros [|[] b2] L; try discriminate; cbn; auto. Qed.

Example bits_le_complement_needs_equal_length:
  bits_le [false] [false; false] = true /\ bits_le [true] [true; true] = true.
Proof. split; reflexivity. Qed.
