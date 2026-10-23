(** * Is CaseInsensitiveMap's hash consistent with String.equalsIgnoreCase?

    [CimHash.caseInsensitiveHash_correct] proves that the real bytecode of
    [CaseInsensitiveMap.caseInsensitiveHash] computes [cih_spec e u].  A hash
    table is only correct if keys that are equal (here: [equalsIgnoreCase],
    the map's key comparison) have equal hashes.  This file proves:
    - [cih_consistent_bmp]: equal-ignoring-case strings WITHOUT surrogate code
      units have equal hashes, for every Unicode table that satisfies three
      facts the JDK 21 tables satisfy (ASCII case mapping; the Latin-1 letter
      pairs; case mapping keeps BMP characters in the BMP) — checked against
      the real tables by harness/check_unicode_facts.py;
    - [cih_inconsistent_supplementary]: it FAILS for supplementary
      characters: with the JDK's mapping of DESERET CAPITAL/SMALL LETTER LONG I
      (U+10400 / U+10428), the strings "𐐀" and "𐐨" are
      equal ignoring case but get different hashes (the finding of
      docs/finding-cim-supplementary-case.md, here as a theorem). *)

From Stdlib Require Import ZArith String List Bool Lia.
From JVM.Core Require Import Int Instr Desc Semantics Machine.
From JVM.Jdk Require Import Strings Jdk.
From JVM.Camel Require Import CimHash.
Import ListNotations.
Open Scope Z_scope.

Definition latin1_facts (u : uenv) : Prop :=
  forall x, 192 <= x <= 222 -> x <> 215 -> u_upper u x = x /\ u_upper u (x + 32) = x.

Definition bmp_closed (u : uenv) : Prop :=
  forall c, 0 <= c < 65536 -> 0 <= u_upper u c < 65536 /\ 0 <= u_lower u c < 65536.

Definition jdk_facts (u : uenv) : Prop := uenv_ascii u /\ latin1_facts u /\ bmp_closed u.

Definition no_surrogates (s : list Z) : Prop := Forall (fun c => 0 <= c < 65536 /\ is_surrogate c = false) s.

Section Consistency.
Variable e : jenv.
Let u := j_u e.
Hypothesis F : jdk_facts u.

Lemma i2c_id : forall c, 0 <= c < 65536 -> i2c c = c.
Proof. intros. unfold i2c. apply Z.mod_small. simpl. lia. Qed.

Lemma wrap32_small : forall c, 0 <= c < 65536 -> wrap 32 c = c.
Proof. intros. apply wrap_id; unfold in_range; simpl; lia. Qed.

(** On BMP characters the per-character fold is lower(upper(c)). *)
Lemma fold_char_spec : forall c, 0 <= c < 65536 -> fold_char e c = u_lower u (u_upper u c).
Proof.
  intros c Hc. destruct F as (Fa & Fl & Fb).
  unfold fold_char. fold u.
  destruct (c <? 65) eqn:E1; destruct (90 <? c) eqn:E2; simpl;
    try (apply Z.ltb_lt in E1); try (apply Z.ltb_ge in E1);
    try (apply Z.ltb_lt in E2); try (apply Z.ltb_ge in E2).
  - (* c < 65 and c > 90: impossible *) lia.
  - (* c < 65: ASCII, not a letter *)
    replace (c <? 128) with true by (symmetry; apply Z.ltb_lt; lia).
    destruct (Fa c ltac:(lia)) as [Hu Hl]. fold u in Hu, Hl. rewrite Hu. unfold ascii_upper.
    replace ((97 <=? c) && (c <=? 122)) with false by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia).
    destruct (Fa c ltac:(lia)) as [_ Hl']. fold u in Hl'. rewrite Hl'. unfold ascii_lower.
    replace ((65 <=? c) && (c <=? 90)) with false by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia).
    reflexivity.
  - destruct (c <? 128) eqn:E3.
    + apply Z.ltb_lt in E3.
      destruct (Fa c ltac:(lia)) as [Hu _]. fold u in Hu. rewrite Hu. unfold ascii_upper.
      destruct ((97 <=? c) && (c <=? 122)) eqn:E4.
      * apply andb_true_iff in E4 as [E4 E5]. apply Z.leb_le in E4. apply Z.leb_le in E5.
        destruct (Fa (c - 32) ltac:(lia)) as [_ Hl]. fold u in Hl. rewrite Hl. unfold ascii_lower.
        replace ((65 <=? c - 32) && (c - 32 <=? 90)) with true by (symmetry; apply andb_true_iff; split; apply Z.leb_le; lia).
        lia.
      * destruct (Fa c ltac:(lia)) as [_ Hl]. fold u in Hl. rewrite Hl. unfold ascii_lower.
        replace ((65 <=? c) && (c <=? 90)) with false by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
        reflexivity.
    + apply Z.ltb_ge in E3.
      destruct (Fb c Hc) as [Hu _]. fold u in Hu. rewrite (i2c_id (u_upper u c)) by lia.
      destruct (Fb (u_upper u c) Hu) as [_ Hl]. rewrite i2c_id by lia. reflexivity.
  - (* 'A'..'Z' *)
    destruct (Fa c ltac:(lia)) as [Hu _]. fold u in Hu. rewrite Hu. unfold ascii_upper.
    replace ((97 <=? c) && (c <=? 122)) with false by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia).
    destruct (Fa c ltac:(lia)) as [_ Hl]. fold u in Hl. rewrite Hl. unfold ascii_lower.
    replace ((65 <=? c) && (c <=? 90)) with true by (symmetry; apply andb_true_iff; split; apply Z.leb_le; lia).
    rewrite wrap32_small by lia. rewrite i2c_id by lia. reflexivity.
Qed.

Definition fold_eq (c1 c2 : Z) : Prop := u_lower u (u_upper u c1) = u_lower u (u_upper u c2).

Lemma cp_eq_ci_fold : forall c1 c2, cp_eq_ci u c1 c2 = true -> fold_eq c1 c2.
Proof.
  intros c1 c2 H. unfold cp_eq_ci, fold_eq in *. apply orb_true_iff in H as [H|H];
  apply Z.eqb_eq in H; [rewrite H | ]; auto.
Qed.

Definition latin1_case_pair (c1 c2 : Z) : bool :=
  negb (latin1_eq_ci c1 c2) || (c1 =? c2) ||
  (let x := Z.land c1 223 in
   (((65 <=? x) && (x <=? 90)) || ((192 <=? x) && (x <=? 222) && negb (x =? 215)))
   && ((c1 =? x) || (c1 =? x + 32)) && ((c2 =? x) || (c2 =? x + 32))).

Lemma forallb_range : forall (f : Z -> bool) n,
  forallb f (map Z.of_nat (seq 0 n)) = true -> forall c, 0 <= c < Z.of_nat n -> f c = true.
Proof.
  intros f n H c Hc. rewrite forallb_forall in H. apply H.
  apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia.
Qed.

Lemma latin1_case_pair_all :
  forallb (fun c1 => forallb (fun c2 => latin1_case_pair c1 c2) (map Z.of_nat (seq 0 256)))
          (map Z.of_nat (seq 0 256)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma latin1_fold : forall c1 c2, 0 <= c1 < 256 -> 0 <= c2 < 256 -> latin1_eq_ci c1 c2 = true -> fold_eq c1 c2.
Proof.
  intros c1 c2 H1 H2 H. destruct F as (Fa & Fl & Fb).
  assert (P := forallb_range _ _ latin1_case_pair_all c1 ltac:(simpl; lia)).
  cbv beta in P. assert (P2 := forallb_range _ _ P c2 ltac:(simpl; lia)).
  unfold latin1_case_pair in P2. rewrite H in P2. simpl negb in P2.
  unfold fold_eq.
  destruct (Z.eqb_spec c1 c2) as [->|Hne]; [reflexivity|].
  rewrite orb_false_l in P2.
  set (x := Z.land c1 223) in *.
  apply andb_true_iff in P2 as [P2 Hc2]. apply andb_true_iff in P2 as [Hx Hc1].
  assert (Hux : u_upper u x = x /\ u_upper u (x + 32) = x).
  { apply orb_true_iff in Hx as [Hx|Hx].
    - apply andb_true_iff in Hx as [Ha Hb]. apply Z.leb_le in Ha. apply Z.leb_le in Hb.
      destruct (Fa x ltac:(lia)) as [U1 _]. destruct (Fa (x + 32) ltac:(lia)) as [U2 _].
      fold u in U1, U2. rewrite U1, U2. unfold ascii_upper.
      replace ((97 <=? x) && (x <=? 122)) with false by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia).
      replace ((97 <=? x + 32) && (x + 32 <=? 122)) with true by (symmetry; apply andb_true_iff; split; apply Z.leb_le; lia).
      split; lia.
    - apply andb_true_iff in Hx as [Hx Hn]. apply andb_true_iff in Hx as [Ha Hb].
      apply Z.leb_le in Ha. apply Z.leb_le in Hb. apply negb_true_iff in Hn. apply Z.eqb_neq in Hn.
      apply Fl; lia. }
  destruct Hux as [U1 U2].
  apply orb_true_iff in Hc1 as [Hc1|Hc1]; apply Z.eqb_eq in Hc1;
  apply orb_true_iff in Hc2 as [Hc2|Hc2]; apply Z.eqb_eq in Hc2;
  rewrite Hc1, Hc2; rewrite ?U1, ?U2; reflexivity.
Qed.

(** Pointwise fold equality gives equal hashes. *)
Lemma hash_pointwise : forall a b, Forall2 fold_eq a b -> no_surrogates a -> no_surrogates b ->
  forall h, fold_left (hstep e) a h = fold_left (hstep e) b h.
Proof.
  intros a b H. induction H as [|c1 c2 a b Hc Hab IH]; intros Na Nb h; [reflexivity|].
  inversion Na as [|? ? [Ra _] Na']; inversion Nb as [|? ? [Rb _] Nb']; subst.
  simpl. assert (E : hstep e h c1 = hstep e h c2)
    by (unfold hstep; rewrite (fold_char_spec c1 Ra), (fold_char_spec c2 Rb), Hc; reflexivity).
  rewrite E. apply IH; auto.
Qed.

Lemma latin1_eqs_fold : forall a b, Forall (fun c => 0 <= c < 256) a -> Forall (fun c => 0 <= c < 256) b ->
  length a = length b -> latin1_eqs a b = true -> Forall2 fold_eq a b.
Proof.
  induction a as [|c1 a IH]; intros [|c2 b] Ha Hb Hl H; simpl in *; try discriminate; auto.
  inversion Ha as [|? ? Ra Ha']; inversion Hb as [|? ? Rb Hb']; subst.
  apply andb_true_iff in H as [HA HB].
  constructor; [apply latin1_fold; auto | apply IH; auto].
Qed.

Lemma mixed_fold : forall a b, length a = length b -> mixed_eq_ci u a b = true -> Forall2 fold_eq a b.
Proof.
  induction a as [|c1 a IH]; intros [|c2 b] Hl H; simpl in *; try discriminate; auto.
  apply andb_true_iff in H as [HA HB]. constructor; [|apply IH; auto].
  unfold fold_eq. apply orb_true_iff in HA as [HA|HA]; [apply Z.eqb_eq in HA; subst; reflexivity|].
  apply orb_true_iff in HA as [HA|HA]; apply Z.eqb_eq in HA; [rewrite HA|]; auto.
Qed.

Lemma utf16_fold : forall fuel a b pa pb, no_surrogates a -> no_surrogates b -> length a = length b ->
  (length a <= fuel)%nat -> utf16_eq_ci u fuel pa pb a b = true -> Forall2 fold_eq a b.
Proof.
  induction fuel as [|fuel IH]; intros a b pa pb Na Nb Hl Hf H.
  - destruct a; simpl in *; [destruct b; [constructor | discriminate] | lia].
  - destruct a as [|c1 a]; destruct b as [|c2 b]; simpl in Hl; try discriminate; [constructor|].
    inversion Na as [|? ? [_ S1] Na']; inversion Nb as [|? ? [_ S2] Nb']; subst.
    simpl in H.
    destruct ((c1 =? c2) || cp_eq_ci u c1 c2) eqn:E.
    + constructor.
      * apply orb_true_iff in E as [E|E]; [apply Z.eqb_eq in E; subst; reflexivity | apply cp_eq_ci_fold; auto].
      * eapply IH; eauto. simpl in Hf. lia.
    + assert (S1' : is_surrogate c1 = false) by (inversion Na as [|? ? [_ X] _]; exact X).
      assert (S2' : is_surrogate c2 = false) by (inversion Nb as [|? ? [_ X] _]; exact X).
      rewrite S1', S2' in H. simpl in H.
      apply orb_false_iff in E as [_ E]. rewrite E in H. discriminate.
Qed.

(** equalsIgnoreCase on surrogate-free strings implies equal caseInsensitiveHash. *)
Theorem cih_consistent_bmp : forall a b, no_surrogates a -> no_surrogates b ->
  equals_ignore_case u a b = true -> cih_spec e a = cih_spec e b.
Proof.
  intros a b Na Nb H. unfold equals_ignore_case in H. apply andb_true_iff in H as [Hl H].
  apply Z.eqb_eq in Hl. unfold slen in Hl. apply Nat2Z.inj in Hl.
  assert (FE : Forall2 fold_eq a b).
  { destruct (is_latin1 a) eqn:La; destruct (is_latin1 b) eqn:Lb.
    - apply latin1_eqs_fold; auto.
      + unfold is_latin1 in La. rewrite forallb_forall in La. apply Forall_forall. intros c Hc.
        specialize (La c Hc). apply Z.ltb_lt in La. unfold no_surrogates in Na. rewrite Forall_forall in Na. destruct (Na c Hc). lia.
      + unfold is_latin1 in Lb. rewrite forallb_forall in Lb. apply Forall_forall. intros c Hc.
        specialize (Lb c Hc). apply Z.ltb_lt in Lb. unfold no_surrogates in Nb. rewrite Forall_forall in Nb. destruct (Nb c Hc). lia.
    - apply mixed_fold; auto.
    - apply Forall2_flip. eapply Forall2_impl; [ | apply mixed_fold; [lia | exact H]].
      intros x y Hxy. unfold fold_eq in *. symmetry. exact Hxy.
    - apply (utf16_fold (S (length a)) a b None None); auto. }
  unfold cih_spec. rewrite (hash_pointwise a b FE Na Nb 0). reflexivity.
Qed.

End Consistency.

(** ** The supplementary-character counterexample.
    Any Unicode table in which U+10400 and U+10428 are a case pair (as in
    JDK 21) and surrogate code units map to themselves (as in JDK 21) breaks
    the consistency. *)
Theorem cih_inconsistent_supplementary : forall e,
  u_upper (j_u e) 66600 = 66560 ->      (* toUpperCase(U+10428) = U+10400 *)
  u_upper (j_u e) 66560 = 66560 ->      (* U+10400 is upper case *)
  (forall c, 55296 <= c <= 57343 -> u_upper (j_u e) c = c /\ u_lower (j_u e) c = c) ->
  let a := [55297; 56320] in            (* "𐐀" = U+10400 *)
  let b := [55297; 56360] in            (* "𐐨" = U+10428 *)
  equals_ignore_case (j_u e) a b = true /\ cih_spec e a <> cih_spec e b.
Proof.
  intros e H1 H2 Hs a b. split.
  - unfold equals_ignore_case. cbn -[u_upper u_lower].
    destruct (Hs 56320 ltac:(lia)) as [Ua La]. destruct (Hs 56360 ltac:(lia)) as [Ub Lb].
    unfold cp_eq_ci. rewrite Ua, Ub. cbn. rewrite H1, H2, La, Lb. reflexivity.
  - unfold cih_spec, hstep, fold_char. cbn -[u_upper u_lower wrap i2c].
    destruct (Hs 55297 ltac:(lia)) as [U1 L1]. destruct (Hs 56320 ltac:(lia)) as [U2 L2].
    destruct (Hs 56360 ltac:(lia)) as [U3 L3].
    rewrite U1, U2, U3. cbn -[u_lower wrap]. rewrite L1, L2, L3. vm_compute. discriminate.
Qed.
