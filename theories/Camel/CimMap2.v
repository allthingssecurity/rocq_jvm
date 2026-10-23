(** * CaseInsensitiveMap (fix): put of a new key with a free slot, at the level of the map. *)

From Stdlib Require Import ZArith String List Bool Lia.
From JVM.Core Require Import Int Instr Desc Semantics Machine Logic.
From JVM.Jdk Require Import Strings Jdk.
From JVM.Camel Require Import CimProg CimCalls CimPut CimRemove CimCompact CimAbs CimAbs2 CimMap.
Import ListNotations.
Open Scope Z_scope.

Lemma Lv_snoc : forall ks f i, Lv ks i (S f) = app (Lv ks i f) (if nonnull (nth_z ks (i + Z.of_nat f)) then [i + Z.of_nat f] else []).
Proof.
  intros ks f. induction f as [|f IH]; intros i.
  - rewrite Lv_S. cbn. rewrite Z.add_0_r. destruct (nonnull (nth_z ks i)); reflexivity.
  - rewrite Lv_S, (Lv_S ks i f), IH. replace (i + 1 + Z.of_nat f) with (i + Z.of_nat (S f)) by lia.
    destruct (nonnull (nth_z ks i)); reflexivity.
Qed.

Lemma Lv_set_out : forall ks x X f i, (forall p, i <= p < i + Z.of_nat f -> p <> x) -> Lv (set_nth_z ks x X) i f = Lv ks i f.
Proof.
  intros ks x X f. induction f as [|f IH]; intros i H; [reflexivity|].
  rewrite !Lv_S. rewrite nth_set_other by (apply not_eq_sym; apply H; lia).
  rewrite IH by (intros p Hp; apply H; lia). reflexivity.
Qed.

Section Map2.
Variable e : jenv.
Variable good : list Z -> Prop.
Hypothesis eq_sym : forall a b, good a -> good b -> eqic e a b = eqic e b a.
Hypothesis eq_trans : forall a b c, good a -> good b -> good c -> eqic e a b = true -> eqic e b c = true -> eqic e a c = true.
Hypothesis eq_hash : forall a b, good a -> good b -> eqic e a b = true -> cih_spec e a = cih_spec e b.

(** put of a key that is not in the map, when the slot arrays have a free slot at the end
    and no resize is due: the entry is appended to the map. *)
Theorem put_new_free_map : forall h n sts ini lk m k ku v
    tA kA vA cA sz u af tbl ks vs cn pw thr,
  (* the representation, with its internal slot counter [u] *)
  h m = Some (OObj CIM (cim_fields tA kA vA cA sz u thr af)) ->
  h tA = Some (OArr TInt tbl) -> h kA = Some (OArr (TRef STR) ks) ->
  h vA = Some (OArr (TRef OBJ) vs) -> h cA = Some (OArr TInt cn) -> tA <> cA ->
  Z.of_nat (length tbl) = 2 ^ pw -> 0 <= pw <= 30 ->
  length vs = length ks -> length cn = length ks -> Z.of_nat (length ks) <= MAX_ARRAY ->
  0 <= u -> slots_ok ks 0 (Z.to_nat u) ->
  (forall q, u <= q < Z.of_nat (length ks) -> nth_z ks q = Some VNull) ->
  sz = Z.of_nat (length (Lv ks 0 (Z.to_nat u))) ->
  tbl_ok e h ks cn tbl pw (Lv ks 0 (Z.to_nat u)) -> keys_ok e good h ks (Lv ks 0 (Z.to_nat u)) -> allrefs vs ->
  (* the call *)
  h k = Some (OStr ku) -> slen ku <= INT_MAX -> good ku ->
  erroneous cp 64 sts CIM = false -> init_needed cp 64 ini CIM = None -> assoc KNOWN sts = Some VNull ->
  vok h v -> (match v with VRef vl => vl <> m /\ (forall t es, h vl <> Some (OArr t es)) | _ => True end) ->
  a_mem e h (entries ks vs (Lv ks 0 (Z.to_nat u))) ku = false ->
  sz < thr -> thr <= INT_MAX -> u < Z.of_nat (length ks) ->
  returns cp (mdl e) {| ms_heap := h; ms_next := n; ms_statics := sts; ms_inited := ini; ms_locks := lk;
                         ms_frames := [put_frame m k v] |}
    (Some VNull)
    (fun s' => cim_rep e good (ms_heap s') m (app (entries ks vs (Lv ks 0 (Z.to_nat u))) [(k, v)]) (length ks) thr /\
               same_strings (ms_heap s') h /\ ms_next s' = n /\ ms_statics s' = sts /\ ms_inited s' = ini).
Proof.
  intros h n sts ini lk m k ku v tA kA vA cA sz u af tbl ks vs cn pw thr
         Hm HtA HkA HvA HcA Htc Hlen Hpw Hlv Hlc HKmax Hu0 Hsl Hnull Hsz Htbl Hkeys Hrefs
         Hk Hmax Hg He Hi HK Hv Hvd Hmem Hthr Hthr' Hfree.
  set (S := Lv ks 0 (Z.to_nat u)) in *.
  destruct (find_correct e good eq_hash h ks cn tbl pw S ku Htbl Hkeys Hg ltac:(lia)) as (i & L & Hb & Hc & HlL & Hres).
  pose proof Htbl as (Hkd & Ht).
  assert (Hbb : 0 <= bucket e ku pw < 2 ^ pw) by (unfold bucket; apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia).
  destruct (Ht _ Hbb) as (i' & L' & Hb' & Hc' & Hnd' & Hm').
  rewrite Hb in Hb'. injection Hb' as <-. assert (HL : L = L') by (eapply chain_unique; eassumption). subst L'.
  assert (HkL : keyed h ks L) by (intros s Hs; apply Hkd; apply Hm' in Hs; tauto).
  assert (Hw : fi_walk e h ks cn ku i (Datatypes.S (length ks)) = Some (first_match e h ks ku L))
    by (apply fi_walk_chain; [exact Hc | exact HkL | lia]).
  (* the key is not in the map *)
  assert (Hno : forall s, ~ holds e h ks S ku s).
  { intros s Hs. assert (Hm2 : a_mem e h (entries ks vs S) ku = true)
      by (apply (a_mem_entries e h ks vs S ku Hkd S (fun x Hx => Hx)); exists s; split; [destruct Hs; assumption | exact Hs]).
    congruence. }
  assert (Hfm : first_match e h ks ku L = -1).
  { destruct Hres as [(H1 & _) | H1]; [exact H1 | exfalso; exact (Hno _ H1)]. }
  rewrite Hfm in Hw.
  assert (HuS : ~ In u S) by (intro H; apply Lv_range in H; lia).
  assert (HszI : 0 <= sz) by lia.
  assert (Hvd' : match v with VRef vl => vl <> m /\ vl <> kA | _ => True end).
  { destruct v as [z|z|z|z| |vl|]; try exact I. destruct Hvd as (V1 & V2). split; [exact V1|].
    intro E. subst vl. exact (V2 _ _ HkA). }
  eapply returns_weaken.
  { apply (put_new_fast e h n sts ini lk m k v tA kA vA cA sz u thr af tbl ks vs cn pw ku i); try assumption;
      first [ lia | (change MAX_ARRAY with 1048576 in HKmax; change INT_MAX with 2147483647; lia) ]. }
  cbv zeta. intros s' (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
  set (b := cih_spec e ku mod 2 ^ pw) in *.
  set (h' := ms_heap s') in *.
  (* the strings are the same *)
  assert (Hsame : same_strings h' h).
  { intros y u0. destruct (Z.eq_dec y m) as [->|N1]; [rewrite P1, Hm; split; discriminate|].
    destruct (Z.eq_dec y kA) as [->|N2]; [rewrite P2, HkA; split; discriminate|].
    destruct (Z.eq_dec y vA) as [->|N3]; [rewrite P3, HvA; split; discriminate|].
    destruct (Z.eq_dec y cA) as [->|N4]; [rewrite P4, HcA; split; discriminate|].
    destruct (Z.eq_dec y tA) as [->|N5]; [rewrite P5, HtA; split; discriminate|].
    rewrite P6 by assumption. reflexivity. }
  assert (Hsame' : same_strings h h') by (intros y u0; symmetry; apply Hsame).
  split; [|split; [exact Hsame | auto]].
  assert (HLv' : Lv (set_nth_z ks u (VRef k)) 0 (Z.to_nat (u + 1)) = app S [u]).
  { replace (Z.to_nat (u + 1)) with (Datatypes.S (Z.to_nat u)) by lia. rewrite Lv_snoc.
    replace (0 + Z.of_nat (Z.to_nat u)) with u by lia. rewrite nth_set_same by lia. cbn [nonnull].
    rewrite Lv_set_out by (intros p Hp; lia). reflexivity. }
  exists tA, kA, vA, cA, (sz + 1), (u + 1), af, (set_nth_z tbl b (VInt u)), (set_nth_z ks u (VRef k)),
         (set_nth_z vs u v), (set_nth_z cn u (VInt i)), pw.
  refine (conj P1 (conj P5 (conj P2 (conj P3 (conj P4 (conj Htc _)))))).
  rewrite !set_nth_len. split; [exact Hlen|]. split; [exact Hpw|].
  split; [reflexivity|]. split; [exact Hlv|]. split; [exact Hlc|]. split; [exact HKmax|]. split; [lia|].
  split.
  { intros q Hq. destruct (Z.eq_dec q u) as [->|Hne].
    - right. exists k. apply nth_set_same. lia.
    - rewrite nth_set_other by congruence. apply Hsl. lia. }
  split.
  { intros q Hq. rewrite nth_set_other by lia. apply Hnull. lia. }
  rewrite HLv'. split; [rewrite app_length; cbn [length]; lia|].
  split.
  { apply (tbl_ok_same e h h'); [exact Hsame'|].
    apply insert_ok; try assumption; lia. }
  split.
  { apply (keys_ok_same e good h h'); [exact Hsame'|].
    apply (insert_keys_ok e good eq_sym h ks S u k ku); try assumption; lia. }
  split.
  { apply allrefs_set; [exact Hrefs | destruct v; try contradiction; reflexivity]. }
  unfold entries. rewrite map_app. cbn [map]. f_equal.
  - symmetry. apply entries_set_other; [lia|]. intros s0 Hs0. pose proof (Lv_range _ _ _ _ Hs0). split; lia.
  - f_equal. f_equal.
    + unfold key_ref. rewrite nth_set_same by lia. reflexivity.
    + symmetry. apply nth_set_nat_same; lia.
Qed.

End Map2.
