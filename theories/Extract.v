(** * Extraction of the loader and interpreter to OCaml, for differential testing.

    The extracted code is used only by the differential harness
    (harness/model_main.ml); proofs never depend on it.  We use the standard
    extraction of [bool], [option], [list], [prod] to OCaml's types and of
    [ascii]/[string] to OCaml [char]/[string]; [Z], [positive] and [nat]
    keep their Rocq (unary/binary) representation, so no OCaml machine
    arithmetic is trusted. *)

From Stdlib Require Import ZArith String Ascii List.
From Stdlib Require Extraction ExtrOcamlBasic ExtrOcamlNativeString.
From JVM.Core Require Import Int Instr Desc Semantics Float.
From JVM.Loader Require Import ClassFile.
From JVM.Core Require Import Machine Threads.
From JVM.Jdk Require Import Strings Jdk.

(** Decimal conversions used by the harness to read and print values. *)
Fixpoint digits_val (s : string) (acc : Z) : Z :=
  match s with
  | EmptyString => acc
  | String c r => digits_val r (acc * 10 + (Z.of_nat (nat_of_ascii c) - 48))
  end.

Definition z_of_string (s : string) : Z :=
  match s with
  | String c r => if Ascii.eqb c "-"%char then - digits_val r 0 else digits_val s 0
  | EmptyString => 0
  end.

Fixpoint z_digits (fuel : nat) (z : Z) (acc : string) : string :=
  match fuel with
  | O => acc
  | S k =>
    let acc' := String (ascii_of_nat (48 + Z.to_nat (z mod 10))) acc in
    if z <? 10 then acc' else z_digits k (z / 10) acc'
  end.

Definition z_to_string (z : Z) : string :=
  if z <? 0 then String "-"%char (z_digits 40 (- z) EmptyString) else z_digits 40 z EmptyString.

Example zs1 : z_to_string (-9223372036854775808) = "-9223372036854775808"%string. Proof. reflexivity. Qed.
Example zs2 : z_of_string "-2147483648" = -2147483648. Proof. reflexivity. Qed.

(** The thread layer, for the thread tests (harness/threads_main.ml). *)
Definition call_static_args_threads (p : program) (mdl : model) (sch : scheduler) (fuel : nat) (cls name desc : string)
           (xs : list jarg) : tresult :=
  let s0 := {| ms_heap := fun _ => None; ms_next := 1; ms_statics := nil; ms_inited := nil;
               ms_locks := nil; ms_frames := nil |} in
  let (vs, s1) := alloc_args s0 xs in
  match entry_state cls name desc vs with
  | Some s => trun p mdl sch fuel O (tm_of {| ms_heap := ms_heap s1; ms_next := ms_next s1; ms_statics := nil;
                                            ms_inited := nil; ms_locks := nil; ms_frames := ms_frames s |})
  | None => TRStuckRun "entry: bad descriptor or arguments"
  end.

Definition tm_ms (tm : tmstate) : mstate :=
  {| ms_heap := tm_heap tm; ms_next := tm_next tm; ms_statics := tm_statics tm; ms_inited := tm_inited tm;
     ms_locks := nil; ms_frames := nil |}.

Set Extraction Output Directory "extraction".
Extraction "jvm.ml" parse_class load_method find_method invoke_static parse_mdesc
  z_of_string z_to_string INT_MIN
  load_program call_static base_model exn_class
  jdk_model call_static_args str_value Float.canon32 Float.canon64
  call_static_args_threads tm_ms.
