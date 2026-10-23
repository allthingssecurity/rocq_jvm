(** * camel-wal TransactionLog (fix): the ring-buffer invariant, preserved by [add].

    [wal_inv cap n s t arr C L] says: the heap of [s] holds the log [t] after
    [n] adds into a ring of capacity [cap]: its fields are (cur_index, cur_layer)
    of [WalSpec], its array has [cap] slots and slot [ent_index cap k] holds the
    container [C k] of every entry k still in the ring, and the LayerInfo
    [L k] of every added entry k carries (ent_index cap k, ent_layer cap k).

    [add_preserves]: running the real bytecode of [add] (with the LayerInfo and
    EntryContainer constructors and Object.<init>) on such a state returns the
    new container and gives [wal_inv] for n + 1.  So the invariant holds after
    every sequence of adds, and [update_contract] (WalUpdateSpec) applies to
    every entry ever added: see [wal_update]. *)

From Stdlib Require Import ZArith String List Bool Lia.
From JVM.Core Require Import Int Instr Desc Semantics Machine Logic.
From JVM.Jdk Require Import Strings Jdk.
From JVM.Camel Require Import WalSpec WalUpdate WalUpdateSpec WalAdd.
Import ListNotations.
Open Scope Z_scope.

(** ** Arrays *)
Lemma set_nth_z_length : forall {A} (l : list A) i v, length (set_nth_z l i v) = length l.
Proof. induction l as [|x r IH]; intros i v; cbn; [reflexivity|]. destruct (i =? 0); cbn; [reflexivity|]. now rewrite IH. Qed.

Lemma nth_set_same : forall {A} (l : list A) i v, 0 <= i < Z.of_nat (length l) -> nth_z (set_nth_z l i v) i = Some v.
Proof.
  induction l as [|x r IH]; intros i v Hi; cbn in *; [lia|].
  destruct (Z.eqb_spec i 0); cbn.
  - subst. reflexivity.
  - replace (i =? 0) with false by (symmetry; apply Z.eqb_neq; assumption). apply IH. lia.
Qed.

Lemma nth_set_other : forall {A} (l : list A) i j v, i <> j -> nth_z (set_nth_z l i v) j = nth_z l j.
Proof.
  induction l as [|x r IH]; intros i j v Hij; cbn; [reflexivity|].
  destruct (Z.eqb_spec i 0); cbn.
  - replace (j =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
  - destruct (j =? 0); [reflexivity|]. apply IH. lia.
Qed.

(** ** Arithmetic of one add *)
Lemma add_arith : forall cap n, 1 <= cap <= INT_MAX -> 0 <= n -> n / cap <= INT_MAX ->
  (if cap <=? cur_index cap n then 0 else cur_index cap n) = ent_index cap n /\
  (if cap <=? cur_index cap n then wrap 32 (cur_layer cap n + 1) else cur_layer cap n) = ent_layer cap n /\
  ent_index cap n + 1 = cur_index cap (n + 1) /\
  ent_layer cap n = cur_layer cap (n + 1) /\
  0 <= cur_index cap n <= cap.
Proof.
  intros cap n Hcap Hn Hq.
  unfold cur_index, cur_layer, ent_index, ent_layer.
  replace (n + 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (n + 1 - 1) with n by lia.
  pose proof (Z.mod_pos_bound n cap ltac:(lia)) as Bn.
  destruct (Z.eqb_spec n 0) as [E|E].
  - subst n. rewrite Z.mod_0_l, Z.div_0_l by lia.
    replace (cap <=? 0) with false by (symmetry; apply Z.leb_gt; lia). lia.
  - set (m := n - 1).
    pose proof (Z.div_mod m cap ltac:(lia)) as Dm.
    pose proof (Z.mod_pos_bound m cap ltac:(lia)) as Bm.
    set (q := m / cap) in *. set (r := m mod cap) in *.
    destruct (Z.leb_spec cap (r + 1)) as [R|R].
    + (* roll-over: r = cap - 1, n = (q + 1) * cap *)
      assert (Hnq : n / cap = q + 1) by (symmetry; apply (Z.div_unique_pos n cap (q + 1) 0); lia).
      assert (Hnr : n mod cap = 0) by (symmetry; apply (Z.mod_unique_pos n cap (q + 1) 0); lia).
      rewrite Hnq, Hnr. rewrite wrap_id; [lia | lia | unfold in_range, INT_MAX in *; cbn; lia].
    + assert (Hnq : n / cap = q) by (symmetry; apply (Z.div_unique_pos n cap q (r + 1)); lia).
      assert (Hnr : n mod cap = r + 1) by (symmetry; apply (Z.mod_unique_pos n cap q (r + 1)); lia).
      rewrite Hnq, Hnr. lia.
Qed.

(** Two entries that are both in the ring use different slots. *)
Lemma ent_index_ne : forall cap n k, 1 <= cap -> 0 <= k < n -> n + 1 - cap <= k -> ent_index cap k <> ent_index cap n.
Proof.
  intros cap n k Hc Hk Hl. unfold ent_index. intro E.
  pose proof (Z.div_mod n cap ltac:(lia)). pose proof (Z.div_mod k cap ltac:(lia)).
  assert (cap * (n / cap - k / cap) = n - k) by lia.
  assert (0 < n - k < cap) by lia.
  set (d := n / cap - k / cap) in *.
  destruct (Z.le_gt_cases d 0) as [D|D].
  - assert (cap * d <= 0) by nia. lia.
  - assert (cap * 1 <= cap * d) by (apply Z.mul_le_mono_nonneg_l; lia). lia.
Qed.

(** ** The invariant *)
Definition wal_inv (cap n : Z) (s : mstate) (t arr : Z) (C L : Z -> Z) : Prop :=
  1 <= cap <= INT_MAX /\ 0 <= n /\
  ms_heap s t = Some (OObj TL (tl_fields cap arr (cur_index cap n) (cur_layer cap n))) /\
  t < ms_next s /\ arr < ms_next s /\
  (exists es, ms_heap s arr = Some (OArr (TRef EC) es) /\ Z.of_nat (length es) = cap /\
     forall k, 0 <= k < n -> n - cap <= k -> nth_z es (ent_index cap k) = Some (VRef (C k))) /\
  (forall k, 0 <= k < n ->
     C k < ms_next s /\ L k < ms_next s /\ C k <> t /\ C k <> arr /\ L k <> t /\ L k <> arr /\
     (exists b, ms_heap s (L k) = Some (OObj LI (li_fields (ent_index cap k) (ent_layer cap k) b))) /\
     (exists pos le st km kk vm vv,
        ms_heap s (C k) = Some (OObj EC (ec_fields (VRef (L k)) (VRef le) pos)) /\
        ms_heap s le = Some (OObj LE (le_fields st km kk vm vv)) /\ le < ms_next s /\ le <> t /\ le <> arr)).

Definition extend (f : Z -> Z) (n v : Z) : Z -> Z := fun k => if k =? n then v else f k.

Section Ring.
Variable e : jenv.

Theorem add_preserves : forall s t arr cap n C L le st km kk vm vv,
  wal_inv cap n s t arr C L ->
  n / cap <= INT_MAX ->
  ms_frames s = [add_frame t le] ->
  ms_heap s le = Some (OObj LE (le_fields st km kk vm vv)) -> le < ms_next s -> le <> t -> le <> arr ->
  erroneous wp 64 (ms_statics s) EC = false -> init_needed wp 64 (ms_inited s) EC = None ->
  erroneous wp 64 (ms_statics s) LI = false -> init_needed wp 64 (ms_inited s) LI = None ->
  returns wp (mdl e) s (Some (VRef (ms_next s)))
    (fun s' => wal_inv cap (n + 1) s' t arr (extend C n (ms_next s)) (extend L n (ms_next s + 1)) /\
               ms_next s' = ms_next s + 2 /\ ms_statics s' = ms_statics s /\ ms_inited s' = ms_inited s /\
               (forall y, y < ms_next s -> y <> t -> y <> arr -> ms_heap s' y = ms_heap s y)).
Proof.
  intros s t arr cap n C L le st km kk vm vv Hinv Hq Hfr Hle Hle' Hlt Hla He1 Hi1 He2 Hi2.
  destruct Hinv as (Hcap & Hn & Ht & Ht' & Ha' & (es & Ha & Hlen & Hslots) & Hents).
  destruct (add_arith cap n Hcap Hn Hq) as (A1 & A2 & A3 & A4 & A5).
  pose proof (add_step e s t le cap arr (cur_index cap n) (cur_layer cap n) es Hfr Ht Ha Hlen (ltac:(lia) : 0 < cap <= INT_MAX) A5 Ht' Ha'
                He1 Hi1 He2 Hi2) as R.
  cbv zeta in R. rewrite A1, A2 in R.
  eapply returns_weaken; [exact R|].
  intros s' (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  set (n0 := ms_next s) in *.
  assert (Hta : t <> arr) by (intro E; subst arr; rewrite Ht in Ha; discriminate).
  split; [|split; [exact P5 | split; [assumption | split; assumption]]].
  unfold wal_inv. rewrite P5.
  split; [exact Hcap|]. split; [lia|].
  split; [rewrite P1, A3, A4; reflexivity|].
  split; [lia|]. split; [lia|].
  split.
  - exists (set_nth_z es (ent_index cap n) (VRef n0)). split; [exact P2|]. split; [rewrite set_nth_z_length; exact Hlen|].
    intros k Hk Hl. unfold extend. destruct (Z.eqb_spec k n) as [E|E].
    + subst k. apply nth_set_same. rewrite Hlen. unfold ent_index. pose proof (Z.mod_pos_bound n cap ltac:(lia)). lia.
    + rewrite nth_set_other by (apply not_eq_sym; apply ent_index_ne; lia).
      apply Hslots; lia.
  - intros k Hk. unfold extend. destruct (Z.eqb_spec k n) as [E|E].
    + subst k. assert (t < n0 /\ arr < n0) by lia.
      repeat split; try lia.
      * eexists. exact P4.
      * exists (VLong (-1)), le, st, km, kk, vm, vv. split; [exact P3|]. split.
        -- rewrite P8 by lia. exact Hle.
        -- repeat split; try lia; assumption.
    + destruct (Hents k ltac:(lia)) as (C1 & L1 & C2 & C3 & L2 & L3 & (b & Hb) & (pos & le0 & st0 & km0 & kk0 & vm0 & vv0 & Hc & Hl0 & Hl1 & Hl2 & Hl3)).
      repeat split; try lia; try assumption.
      * exists b. rewrite P8 by assumption. exact Hb.
      * exists pos, le0, st0, km0, kk0, vm0, vv0. rewrite !P8 by assumption. repeat split; try lia; assumption.
Qed.

(** The invariant survives any change that keeps every old object or only changes
    the fields of LogEntry objects (what [update] does). *)
Lemma wal_inv_keep : forall cap n s s' t arr C L,
  wal_inv cap n s t arr C L -> ms_next s <= ms_next s' ->
  (forall y, y < ms_next s -> ms_heap s' y = ms_heap s y \/
     exists st km kk vm vv st' km' kk' vm' vv',
       ms_heap s y = Some (OObj LE (le_fields st km kk vm vv)) /\
       ms_heap s' y = Some (OObj LE (le_fields st' km' kk' vm' vv'))) ->
  wal_inv cap n s' t arr C L.
Proof.
  intros cap n s s' t arr C L (Hcap & Hn & Ht & Ht' & Ha' & (es & Ha & Hlen & Hslots) & Hents) Hnx Hk.
  assert (K : forall y o, y < ms_next s -> ms_heap s y = Some o ->
                (match o with OObj c _ => c <> LE | _ => True end) -> ms_heap s' y = Some o).
  { intros y o Hy Ho Hc. destruct (Hk y Hy) as [E | (st & km & kk & vm & vv & st' & km' & kk' & vm' & vv' & E1 & E2)].
    - rewrite E. exact Ho.
    - rewrite Ho in E1. injection E1 as E3. subst o. exfalso. apply Hc. reflexivity. }
  unfold wal_inv.
  refine (conj Hcap (conj Hn (conj _ (conj _ (conj _ (conj _ _)))))).
  - apply K; [lia | exact Ht | discriminate].
  - lia.
  - lia.
  - exists es. refine (conj _ (conj Hlen Hslots)). apply K; [lia | exact Ha | exact I].
  - intros j Hj.
    destruct (Hents j Hj) as (D1 & M1 & D2 & D3 & M2 & M3 & (bj & Hbj) & (posj & lej & stj & kmj & kkj & vmj & vvj & Hcj & Hlej & Hm1 & Hm2 & Hm3)).
    split; [lia|]. split; [lia|]. refine (conj D2 (conj D3 (conj M2 (conj M3 (conj _ _))))).
    + exists bj. apply K; [lia | exact Hbj | discriminate].
    + destruct (Hk lej Hm1) as [E | (st & km & kk & vm & vv & st' & km' & kk' & vm' & vv' & E1 & E2)].
      * exists posj, lej, stj, kmj, kkj, vmj, vvj.
        split; [apply K; [lia | exact Hcj | discriminate]|]. split; [rewrite E; exact Hlej|]. split; [lia|]. exact (conj Hm2 Hm3).
      * exists posj, lej, st', km', kk', vm', vv'.
        split; [apply K; [lia | exact Hcj | discriminate]|]. split; [exact E2|]. split; [lia|]. exact (conj Hm2 Hm3).
Qed.

(** [update] on the LayerInfo of any added entry k, for a log in the invariant:
    if k is still in the ring it returns k's container and sets the state of k's
    LogEntry; otherwise it returns null and changes nothing.  Either way the
    invariant still holds. *)
Theorem wal_update : forall s t arr cap n C L k stv lg vf,
  wal_inv cap n s t arr C L -> 0 <= k < n -> (n - 1) / cap <= INT_MAX ->
  ms_frames s = [upd_frame t (L k) stv] ->
  (match stv with VNull | VRef _ => true | _ => false end) = true ->
  (match vf with VNull | VRef _ => true | _ => false end) = true ->
  erroneous wp 64 (ms_statics s) TL = false -> init_needed wp 64 (ms_inited s) TL = None ->
  erroneous wp 64 (ms_statics s) ES = false -> init_needed wp 64 (ms_inited s) ES = None ->
  assoc LOGK (ms_statics s) = Some (VRef lg) -> assoc FAILEDK (ms_statics s) = Some vf ->
  ms_heap s lg = Some (OObj LOGC nil) -> lg < ms_next s ->
  if live cap n k then
    returns wp (mdl e) s (Some (VRef (C k)))
      (fun s' => wal_inv cap n s' t arr C L /\ env_same s s' /\ ms_heap s' lg = ms_heap s lg /\
                 exists pos le km kk vm vv,
                   ms_heap s' (C k) = Some (OObj EC (ec_fields (VRef (L k)) (VRef le) pos)) /\
                   ms_heap s' le = Some (OObj LE (le_fields stv km kk vm vv)))
  else
    returns wp (mdl e) s (Some VNull)
      (fun s' => wal_inv cap n s' t arr C L /\ env_same s s' /\ ms_heap s' lg = ms_heap s lg).
Proof.
  intros s t arr cap n C L k stv lg vf Hinv Hk Hq Hfr Hstv Hvf He Hi He2 Hi2 HLOG HF Hlg Hlg'.
  pose proof Hinv as (Hcap & Hn & Ht & Ht' & Ha' & (es & Ha & Hlen & Hslots) & Hents).
  assert (Hr : reachable cap n k) by (unfold reachable; lia).
  pose proof (cu4_live cap n k Hr) as Hcu.
  destruct (Hents k Hk) as (C1 & L1 & C2 & C3 & L2 & L3 & (b & Hb) & (pos & le & st0 & km & kk & vm & vv & Hc & Hle & Hl1 & Hl2 & Hl3)).
  destruct (live cap n k) eqn:Lv.
  - assert (Hs : n - cap <= k) by (unfold live in Lv; apply andb_true_iff in Lv; destruct Lv as [A _]; apply Z.leb_le in A; exact A).
    pose proof (Hslots k Hk Hs) as Hn'.
    assert (Hlgle : lg <> le) by (intro E; subst lg; rewrite Hle in Hlg; discriminate).
    assert (Hcle : C k <> le) by (intro E; rewrite E in Hc; rewrite Hle in Hc; discriminate).
    eapply returns_weaken.
    { eapply (update_live e s t (L k) stv cap arr (cur_index cap n) (cur_layer cap n) (ent_index cap k) (ent_layer cap k) b lg es (C k) (VRef (L k)) pos le st0 km kk vm vv);
        try eassumption.
      unfold ent_index. pose proof (Z.mod_pos_bound k cap ltac:(lia)). lia. }
    intros s' (P1 & P2 & P3).
    assert (Hnx : ms_next s <= ms_next s') by apply P3.
    refine (conj _ (conj P3 (conj (P2 lg Hlg' Hlgle) _))).
    + apply (wal_inv_keep cap n s s' t arr C L Hinv Hnx).
      intros y Hy. destruct (Z.eq_dec y le) as [E|E].
      * subst y. right. exists st0, km, kk, vm, vv, stv, km, kk, vm, vv. split; assumption.
      * left. apply P2; assumption.
    + exists pos, le, km, kk, vm, vv. rewrite (P2 (C k) C1 Hcle). split; [exact Hc | exact P1].
  - eapply returns_weaken.
    { eapply (update_dead e s t (L k) stv cap arr (cur_index cap n) (cur_layer cap n) (ent_index cap k) (ent_layer cap k) b lg vf);
        eassumption. }
    intros s' (P2 & P3).
    assert (Hnx : ms_next s <= ms_next s') by apply P3.
    refine (conj _ (conj P3 (P2 lg Hlg'))).
    apply (wal_inv_keep cap n s s' t arr C L Hinv Hnx).
    intros y Hy. left. apply P2. exact Hy.
Qed.

(** ** Every sequence of calls *)

Inductive wal_op := OAdd (le : Z) | OUpdate (k : Z) (stv : value).

(** What the calls need from the rest of the program: the classes are initialised, the
    logger and FAILED constants are set. *)
Definition wal_env (s : mstate) (lg : Z) (vf : value) : Prop :=
  erroneous wp 64 (ms_statics s) TL = false /\ init_needed wp 64 (ms_inited s) TL = None /\
  erroneous wp 64 (ms_statics s) ES = false /\ init_needed wp 64 (ms_inited s) ES = None /\
  erroneous wp 64 (ms_statics s) EC = false /\ init_needed wp 64 (ms_inited s) EC = None /\
  erroneous wp 64 (ms_statics s) LI = false /\ init_needed wp 64 (ms_inited s) LI = None /\
  assoc LOGK (ms_statics s) = Some (VRef lg) /\ assoc FAILEDK (ms_statics s) = Some vf /\
  (match vf with VNull | VRef _ => true | _ => false end) = true /\
  ms_heap s lg = Some (OObj LOGC nil) /\ lg < ms_next s.

(** [session ops cap n t C L s]: starting from [s], each call of the sequence, made on
    the log [t] (after [n] adds; entry k has container [C k] and LayerInfo [L k]) returns:
    - [add(le)] for a LogEntry [le]: a new container (the next free address);
    - [update(L k, st)] for an added entry k: k's container if k is still in the ring
      ([live cap n k]), and null otherwise;
    and the rest of the sequence behaves the same from the resulting state. *)
Fixpoint session (ops : list wal_op) (cap n t : Z) (C L : Z -> Z) (s : mstate) : Prop :=
  match ops with
  | nil => True
  | OAdd le :: r =>
      forall st km kk vm vv, ms_heap s le = Some (OObj LE (le_fields st km kk vm vv)) -> le < ms_next s ->
      returns wp (mdl e) (with_frames s [add_frame t le]) (Some (VRef (ms_next s)))
        (fun s' => session r cap (n + 1) t (extend C n (ms_next s)) (extend L n (ms_next s + 1)) s')
  | OUpdate k stv :: r =>
      0 <= k < n -> (match stv with VNull | VRef _ => true | _ => false end) = true ->
      returns wp (mdl e) (with_frames s [upd_frame t (L k) stv])
        (Some (if live cap n k then VRef (C k) else VNull))
        (fun s' => session r cap n t C L s')
  end.

Theorem session_ok : forall ops cap n t arr C L s lg vf,
  wal_inv cap n s t arr C L -> wal_env s lg vf ->
  (n + Z.of_nat (length ops)) / cap <= INT_MAX ->
  session ops cap n t C L s.
Proof.
  induction ops as [|op ops IH]; intros cap n t arr C L s lg vf Hinv Henv Hq; [exact I|].
  pose proof Hinv as (Hcap & Hn & Ht & Ht' & Ha' & (es & Ha & _) & _).
  destruct Henv as (E1 & I1 & E2 & I2 & E3 & I3 & E4 & I4 & HLOG & HF & Hvf & Hlg & Hlg').
  cbn [length] in Hq. rewrite Nat2Z.inj_succ in Hq.
  assert (Hmono : forall a, 0 <= a <= n + Z.of_nat (length ops) + 1 -> a / cap <= INT_MAX).
  { intros a Ha0. eapply Z.le_trans; [ | exact Hq]. apply Z.div_le_mono; lia. }
  assert (Hlgt : lg <> t) by (intro E; subst lg; rewrite Ht in Hlg; discriminate).
  assert (Hlga : lg <> arr) by (intro E; subst lg; rewrite Ha in Hlg; discriminate).
  destruct op as [le | k stv]; cbn [session].
  - intros st km kk vm vv Hle Hle'.
    assert (Hlt : le <> t) by (intro E; subst le; rewrite Ht in Hle; discriminate).
    assert (Hla : le <> arr) by (intro E; subst le; rewrite Ha in Hle; discriminate).
    eapply returns_weaken.
    { apply (add_preserves (with_frames s [add_frame t le]) t arr cap n C L le st km kk vm vv);
        try exact Hinv; try assumption; try reflexivity. apply Hmono. lia. }
    cbn [with_frames ms_next ms_heap ms_statics ms_inited].
    intros s' (P1 & P2 & P3 & P4 & P5).
    eapply IH; [exact P1 | | ].
    + unfold wal_env. rewrite P3, P4.
      refine (conj E1 (conj I1 (conj E2 (conj I2 (conj E3 (conj I3 (conj E4 (conj I4
               (conj HLOG (conj HF (conj Hvf (conj _ _)))))))))))); [rewrite P5 by assumption; exact Hlg | lia].
    + eapply Z.le_trans; [ | exact Hq]. apply Z.div_le_mono; lia.
  - intros Hk Hstv.
    pose proof (wal_update (with_frames s [upd_frame t (L k) stv]) t arr cap n C L k stv lg vf
                  Hinv Hk ltac:(apply Hmono; lia) eq_refl Hstv Hvf E1 I1 E2 I2 HLOG HF Hlg Hlg') as W.
    assert (Post : forall s', wal_inv cap n s' t arr C L -> env_same (with_frames s [upd_frame t (L k) stv]) s' ->
                     ms_heap s' lg = ms_heap s lg -> session ops cap n t C L s').
    { intros s' P1 (Q1 & Q2 & Q3 & Q4 & Q5) P3.
      cbn [with_frames ms_next ms_statics ms_inited] in Q1, Q2, Q3, Q4, Q5.
      eapply IH; [exact P1 | | ].
      - unfold wal_env. rewrite Q2, !Q3, Q4, Q5, P3.
        refine (conj E1 (conj I1 (conj E2 (conj I2 (conj E3 (conj I3 (conj E4 (conj I4
               (conj HLOG (conj HF (conj Hvf (conj Hlg _)))))))))))). lia.
      - eapply Z.le_trans; [ | exact Hq]. apply Z.div_le_mono; lia. }
    destruct (live cap n k).
    + eapply returns_weaken; [exact W|]. intros s' (P1 & P2 & P3 & _). apply Post; assumption.
    + eapply returns_weaken; [exact W|]. intros s' (P1 & P2 & P3). apply Post; assumption.
Qed.

(** From the constructor: [new TransactionLog(cap)] (the object fresh, as after [new])
    followed by any sequence of adds and updates. *)
Theorem wal_from_constructor : forall s t cap lg vf,
  ms_frames s = [tl_init_frame t cap] ->
  ms_heap s t = Some (OObj TL tl_default) -> t < ms_next s ->
  1 <= cap <= MAX_ARRAY ->
  wal_env s lg vf -> lg <> t ->
  returns wp (mdl e) s None
    (fun s' => forall ops, Z.of_nat (length ops) / cap <= INT_MAX ->
               session ops cap 0 t (fun _ => 0) (fun _ => 0) s').
Proof.
  intros s t cap lg vf Hfr Ht Ht' Hcap Henv Hlgt.
  eapply returns_weaken; [ apply (tl_init e s t cap); auto; lia |].
  intros s' (P1 & P2 & P3 & P4 & P5 & P6) ops Hops.
  destruct Henv as (E1 & I1 & E2 & I2 & E3 & I3 & E4 & I4 & HLOG & HF & Hvf & Hlg & Hlg').
  eapply (session_ok ops cap 0 t (ms_next s)).
  - unfold wal_inv. unfold cur_index, cur_layer. cbn [Z.eqb].
    split; [unfold MAX_ARRAY, INT_MAX in *; lia|]. split; [lia|]. split; [exact P1|].
    split; [lia|]. split; [lia|]. split.
    + exists (repeat VNull (Z.to_nat cap)). split; [exact P2|]. split.
      * rewrite repeat_length. lia.
      * intros k Hk. lia.
    + intros k Hk. lia.
  - unfold wal_env. rewrite P4, P5.
    refine (conj E1 (conj I1 (conj E2 (conj I2 (conj E3 (conj I3 (conj E4 (conj I4
             (conj HLOG (conj HF (conj Hvf (conj _ _)))))))))))); [rewrite P6 by lia; exact Hlg | lia].
  - exact Hops.
Qed.

End Ring.
