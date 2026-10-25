(** * The CaseInsensitiveMap programs (main and fix) used by the scenario theorems and
    the unbounded proofs: the real class, the java.util model classes it needs, our driver. *)

From Stdlib Require Import ZArith String List Bool.
From JVM.Core Require Import Int Instr Desc Semantics Machine.
From JVM.Loader Require Import ClassFile.
From JVM.Jdk Require Import Strings Jdk.
From JVM.Classes Require CimMain_CaseInsensitiveMap CimFix_CaseInsensitiveMap CimScenMain CimScenFix CimJdk.
Import ListNotations.
Open Scope Z_scope.

(** Case mapping of ASCII and of the Latin-1 letters (U+00C0..U+00FE except U+00D7, U+00F7;
    U+00DF has no single-char upper case; U+00FF and U+00B5 map out of Latin-1), as in JDK 21. *)
Definition l1_upper (c : Z) : Z :=
  if (97 <=? c) && (c <=? 122) then c - 32
  else if (224 <=? c) && (c <=? 254) && negb (c =? 247) then c - 32
  else if c =? 255 then 376 else if c =? 181 then 924 else c.
Definition l1_lower (c : Z) : Z :=
  if (65 <=? c) && (c <=? 90) then c + 32
  else if (192 <=? c) && (c <=? 222) && negb (c =? 215) then c + 32
  else if c =? 376 then 255 else c.

Definition l1_uenv : uenv := {|
  u_upper := l1_upper; u_lower := l1_lower;
  u_digit := fun c r => if (48 <=? c) && (c <=? 57) && (10 <=? r) then c - 48 else -1;
  u_is_whitespace := fun c => (c =? 32) || ((9 <=? c) && (c <=? 13)) || ((28 <=? c) && (c <=? 31));
  u_is_letter := fun c => ((65 <=? c) && (c <=? 90)) || ((97 <=? c) && (c <=? 122));
  u_is_digit := fun c => (48 <=? c) && (c <=? 57);
  u_is_upper := fun c => (65 <=? c) && (c <=? 90);
  u_is_lower := fun c => (97 <=? c) && (c <=? 122) |}.

Definition env : jenv := {| j_u := l1_uenv; j_log_enabled := fun _ => false; j_ihash := fun l => l |}.

Definition main_files := CimMain_CaseInsensitiveMap.bytes :: CimScenMain.files ++ CimJdk.files.
Definition fix_files := CimFix_CaseInsensitiveMap.bytes :: CimScenFix.files ++ CimJdk.files.

Definition main_prog : program :=
  ltac:(let x := eval vm_compute in (match load_program main_files with Some p => p | None => nil end) in exact x).
Definition fix_prog : program :=
  ltac:(let x := eval vm_compute in (match load_program fix_files with Some p => p | None => nil end) in exact x).

Definition CIM := "org/apache/camel/util/CaseInsensitiveMap"%string.
Definition SCEN := "org/apache/camel/util/CimScenario"%string.

