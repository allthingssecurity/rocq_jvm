(** * CaseInsensitiveMap: unconditional key laws for ASCII strings.

    Character pairs are checked exhaustively in the kernel; induction lifts
    that finite fact to strings of arbitrary length. No Unicode-table facts
    are assumed. The final theorem composes with the real-bytecode hash proof.
    This does not prove the map's resize path or a whole-map session theorem. *)

From Stdlib Require Import ZArith String List Bool Lia.
From JVM.Core Require Import Int Semantics Machine Logic.
From JVM.Jdk Require Import Strings Jdk.
From JVM.Camel Require Import CimHash.
Import ListNotations.
Open Scope Z_scope.

Definition ascii_key (s : units) : Prop := Forall (fun c => 0 <= c < 128) s.
Definition ascii_normalize (s : units) : units := map ascii_lower s.

Lemma ascii_latin1 : forall s, ascii_key s -> is_latin1 s = true.
Proof.
  intros s H. unfold is_latin1. apply forallb_forall.
  intros c Hc. unfold ascii_key in H. rewrite Forall_forall in H.
  apply Z.ltb_lt. specialize (H c Hc). lia.
Qed.

Definition ascii_chars : list Z := map Z.of_nat (seq 0 128).

Lemma ascii_chars_complete : forall c, 0 <= c < 128 -> In c ascii_chars.
Proof.
  intros c H. apply in_map_iff. exists (Z.to_nat c).
  split; [lia | apply in_seq; lia].
Qed.

Lemma ascii_pair_table :
  forallb (fun a => forallb (fun b =>
    Bool.eqb (latin1_eq_ci a b) (ascii_lower a =? ascii_lower b)) ascii_chars)
    ascii_chars = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ascii_pair : forall a b, 0 <= a < 128 -> 0 <= b < 128 ->
  latin1_eq_ci a b = (ascii_lower a =? ascii_lower b).
Proof.
  intros a b Ha Hb. pose proof ascii_pair_table as H.
  rewrite forallb_forall in H. specialize (H a (ascii_chars_complete a Ha)).
  rewrite forallb_forall in H. specialize (H b (ascii_chars_complete b Hb)).
  apply Bool.eqb_prop in H. exact H.
Qed.

Lemma latin1_ascii_normalize : forall a b,
  ascii_key a -> ascii_key b -> length a = length b ->
  latin1_eqs a b = units_eqb (ascii_normalize a) (ascii_normalize b).
Proof.
  induction a as [|x a IH]; intros [|y b] Ha Hb Hl; try discriminate; [reflexivity|].
  inversion Ha as [|? ? Hx Hat]; inversion Hb as [|? ? Hy Hbt]; subst.
  cbn [latin1_eqs ascii_normalize map units_eqb].
  rewrite ascii_pair by assumption. rewrite IH by (auto; simpl in Hl; lia).
  reflexivity.
Qed.

Theorem ascii_equals_iff : forall u a b, ascii_key a -> ascii_key b ->
  (equals_ignore_case u a b = true <-> ascii_normalize a = ascii_normalize b).
Proof.
  intros u a b Ha Hb. unfold equals_ignore_case.
  rewrite (ascii_latin1 a Ha), (ascii_latin1 b Hb).
  rewrite andb_true_iff. split.
  - intros [Hl He]. apply Z.eqb_eq in Hl. unfold slen in Hl.
    apply Nat2Z.inj in Hl. rewrite (latin1_ascii_normalize a b Ha Hb Hl) in He.
    now apply units_eqb_spec in He.
  - intros He. assert (Hl : length a = length b).
    { apply (f_equal (@length Z)) in He. unfold ascii_normalize in He.
      rewrite !length_map in He. exact He. }
    split.
    + unfold slen. rewrite Hl. apply Z.eqb_refl.
    + rewrite (latin1_ascii_normalize a b Ha Hb Hl). apply units_eqb_spec. exact He.
Qed.

Theorem ascii_eq_refl : forall u a, ascii_key a -> equals_ignore_case u a a = true.
Proof. intros. apply ascii_equals_iff; auto. Qed.

Theorem ascii_eq_sym : forall u a b, ascii_key a -> ascii_key b ->
  equals_ignore_case u a b = equals_ignore_case u b a.
Proof.
  intros u a b Ha Hb.
  destruct (equals_ignore_case u a b) eqn:Eab;
  destruct (equals_ignore_case u b a) eqn:Eba; try reflexivity.
  - apply (ascii_equals_iff u a b Ha Hb) in Eab.
    assert (H : equals_ignore_case u b a = true) by (apply ascii_equals_iff; auto).
    congruence.
  - apply (ascii_equals_iff u b a Hb Ha) in Eba.
    assert (H : equals_ignore_case u a b = true) by (apply ascii_equals_iff; auto).
    congruence.
Qed.

Theorem ascii_eq_trans : forall u a b c,
  ascii_key a -> ascii_key b -> ascii_key c ->
  equals_ignore_case u a b = true -> equals_ignore_case u b c = true ->
  equals_ignore_case u a c = true.
Proof.
  intros u a b c Ha Hb Hc Hab Hbc.
  apply (ascii_equals_iff u a b Ha Hb) in Hab.
  apply (ascii_equals_iff u b c Hb Hc) in Hbc.
  apply ascii_equals_iff; auto. congruence.
Qed.

Lemma fold_char_ascii : forall e c, 0 <= c < 128 -> fold_char e c = ascii_lower c.
Proof.
  intros e c Hc. unfold fold_char, ascii_lower.
  destruct (Z.ltb_spec c 65); destruct (Z.ltb_spec 90 c); cbn; try lia.
  - replace (c <? 128) with true by (symmetry; apply Z.ltb_lt; lia).
    replace ((65 <=? c) && (c <=? 90)) with false
      by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia).
    reflexivity.
  - replace (c <? 128) with true by (symmetry; apply Z.ltb_lt; lia).
    replace ((65 <=? c) && (c <=? 90)) with false
      by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
    reflexivity.
  - replace ((65 <=? c) && (c <=? 90)) with true
      by (symmetry; apply andb_true_iff; split; apply Z.leb_le; lia).
    rewrite wrap_id by (unfold in_range; simpl; lia).
    unfold i2c. apply Z.mod_small. simpl. lia.
Qed.

Lemma ascii_hash_fold : forall e a b,
  ascii_key a -> ascii_key b -> ascii_normalize a = ascii_normalize b ->
  forall h, fold_left (hstep e) a h = fold_left (hstep e) b h.
Proof.
  intros e a. induction a as [|x a IH]; intros [|y b] Ha Hb He h;
    try discriminate; [reflexivity|].
  inversion Ha as [|? ? Hx Hat]; inversion Hb as [|? ? Hy Hbt]; subst.
  change (ascii_lower x :: ascii_normalize a = ascii_lower y :: ascii_normalize b) in He.
  injection He as Hxy Hab. cbn [fold_left].
  assert (Hs : hstep e h x = hstep e h y).
  { unfold hstep. rewrite !fold_char_ascii by assumption. now rewrite Hxy. }
  rewrite Hs. apply IH; assumption.
Qed.

Theorem ascii_eq_hash : forall e a b, ascii_key a -> ascii_key b ->
  equals_ignore_case (j_u e) a b = true -> cih_spec e a = cih_spec e b.
Proof.
  intros e a b Ha Hb He. apply (ascii_equals_iff (j_u e) a b Ha Hb) in He.
  unfold cih_spec. now rewrite (ascii_hash_fold e a b Ha Hb He 0).
Qed.

(** The three key hypotheses used by CimAbs, discharged for every jenv. *)
Theorem ascii_key_laws : forall e,
  (forall a b, ascii_key a -> ascii_key b ->
    equals_ignore_case (j_u e) a b = equals_ignore_case (j_u e) b a) /\
  (forall a b c, ascii_key a -> ascii_key b -> ascii_key c ->
    equals_ignore_case (j_u e) a b = true -> equals_ignore_case (j_u e) b c = true ->
    equals_ignore_case (j_u e) a c = true) /\
  (forall a b, ascii_key a -> ascii_key b -> equals_ignore_case (j_u e) a b = true ->
    cih_spec e a = cih_spec e b).
Proof. intro e. repeat split; eauto using ascii_eq_sym, ascii_eq_trans, ascii_eq_hash. Qed.

(** Real bytecode returns a common hash for any two equal ASCII keys. *)
Theorem ascii_bytecode_hash : forall e h n sts ini lk la lb a b,
  ascii_key a -> ascii_key b -> equals_ignore_case (j_u e) a b = true ->
  h la = Some (OStr a) -> h lb = Some (OStr b) ->
  slen a <= INT_MAX -> slen b <= INT_MAX ->
  exists hash,
    returns cim_p (mdl e) (st h n sts ini lk 0 [] [VRef la; VTop; VTop; VTop; VTop])
      (Some (VInt hash)) (fun _ => True) /\
    returns cim_p (mdl e) (st h n sts ini lk 0 [] [VRef lb; VTop; VTop; VTop; VTop])
      (Some (VInt hash)) (fun _ => True).
Proof.
  intros e h n sts ini lk la lb a b Ha Hb He Hla Hlb Hna Hnb.
  exists (cih_spec e a). split.
  - apply caseInsensitiveHash_correct; assumption.
  - rewrite (ascii_eq_hash e a b Ha Hb He). apply caseInsensitiveHash_correct; assumption.
Qed.

Print Assumptions ascii_key_laws.
Print Assumptions ascii_bytecode_hash.
