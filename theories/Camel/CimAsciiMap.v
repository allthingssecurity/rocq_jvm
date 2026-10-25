(** * Instantiate CaseInsensitiveMap's lookup invariant with ASCII keys.
    No caller-supplied equality or hash-consistency hypotheses remain. *)
From Stdlib Require Import ZArith List.
From JVM.Core Require Import Semantics Machine.
From JVM.Camel Require Import CimAbs CimAscii.
Import ListNotations.
Open Scope Z_scope.

Theorem ascii_find_correct : forall e h ks cn tbl pw S q,
  tbl_ok e h ks cn tbl pw S -> keys_ok e ascii_key h ks S ->
  ascii_key q -> 0 <= pw ->
  exists i L, nth_z tbl (bucket e q pw) = Some (VInt i) /\
    chain cn i L /\ (length L <= length cn)%nat /\
    ((first_match e h ks q L = -1 /\ forall s, ~ holds e h ks S q s) \/
      holds e h ks S q (first_match e h ks q L)).
Proof.
  intros. eapply find_correct; eauto using ascii_eq_hash.
Qed.

Print Assumptions ascii_find_correct.
