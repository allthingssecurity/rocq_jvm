(** * CaseInsensitiveMap (fix): the session theorem for ASCII keys, with no hypotheses on
      the key equality.  [CimSession.session_ok] assumes that equalsIgnoreCase is symmetric,
      transitive and consistent with the hash on the keys used; [CimAscii.ascii_key_laws]
      proves these for ASCII strings of any length, for every Unicode environment. *)

From Stdlib Require Import ZArith List.
From JVM.Core Require Import Int Machine.
From JVM.Jdk Require Import Strings Jdk.
From JVM.Camel Require Import CimCalls CimAbs CimMap CimSession CimAscii.
Open Scope Z_scope.

Theorem session_ok_ascii : forall e ops m thr B A K s,
  cim_inv e ascii_key (ms_heap s) (ms_next s) m A K thr -> cim_env s ->
  Z.of_nat K <= B -> 3 * thr <= B -> 3 * thr <= MAX_ARRAY -> thr <= INT_MAX ->
  session e ascii_key ops m thr B A s.
Proof.
  intros e. destruct (ascii_key_laws e) as (Hs & Ht & Hh).
  apply session_ok; unfold eqic; assumption.
Qed.

Print Assumptions session_ok_ascii.
