(** * Fresh bug witnesses on real Camel bytecode (bd4d2ba20d6a).
    FilterIterator runs with an ordinary finite Iterator input.
    TimeUtils runs with a valid normalized Duration heap value; the getters
    execute the real JDK 21.0.11 Duration bytecode. Its constructor/clinit are
    outside this witness. No production method is replaced by a stub. *)
From Stdlib Require Import ZArith String List Bool.
From JVM.Core Require Import Int Instr Desc Semantics Machine.
From JVM.Loader Require Import ClassFile.
From JVM.Jdk Require Import Strings Jdk.
From JVM.Classes Require BugsMain BugsScenario BugsJdk.
Import ListNotations.
Open Scope Z_scope.

Definition bug_p : program :=
  ltac:(let p := eval vm_compute in
    (match load_program (BugsMain.files ++ BugsScenario.files ++ BugsJdk.files) with
     | Some p => p | None => [] end) in exact p).
Definition bug_u : uenv := {| u_upper := ascii_upper; u_lower := ascii_lower;
  u_digit := fun _ _ => -1; u_is_whitespace := fun _ => false;
  u_is_letter := fun _ => false; u_is_digit := fun _ => false;
  u_is_upper := fun _ => false; u_is_lower := fun _ => false |}.
Definition bug_e : jenv := {| j_u := bug_u; j_log_enabled := fun _ => false |}.
Definition bug_mdl := jdk_model bug_p bug_e.
Definition int_result (r : mresult) : option Z :=
  match r with MRValue (Some (VInt i)) _ => Some i | _ => None end.
Definition str_result (r : mresult) : option units :=
  match r with MRValue (Some (VRef l)) s =>
    match ms_heap s l with Some (OStr u) => Some u | _ => None end
  | _ => None end.
Definition filter_remaining (wrap : Z) : option units :=
  str_result (call_static bug_p bug_mdl 10000 "FilterScenario" "afterLookahead"
    "(I)Ljava/lang/String;" [VInt wrap]).
Definition filter_before_next (wrap : Z) : option Z :=
  int_result (call_static bug_p bug_mdl 10000 "FilterScenario" "beforeNext" "(I)I" [VInt wrap]).

(** The same legal next/hasNext/remove sequence removes a through the input
    iterator directly, but removes b through Camel's wrapper. *)
Theorem filter_remove_wrong_element :
  filter_remaining 0 = Some [98;99] /\ filter_remaining 1 = Some [97;99].
Proof. vm_compute. auto. Qed.

(** A direct iterator rejects remove before next; Camel's wrapper accepts it
    after hasNext and reduces the backing collection to two entries. *)
Theorem filter_remove_before_next :
  filter_before_next 0 = Some (-1) /\ filter_before_next 1 = Some 2.
Proof. vm_compute. auto. Qed.

Definition duration_start (seconds nanos : Z) : option mstate :=
  match entry_state "org/apache/camel/util/TimeUtils" "isPositive"
    "(Ljava/time/Duration;)Z" [VRef 1] with
  | None => None
  | Some s => Some {| ms_heap := upd (ms_heap s) 1
      (OObj "java/time/Duration" [("seconds", VLong seconds); ("nanos", VInt nanos)]);
      ms_next := 2; ms_statics := ms_statics s;
      ms_inited := ["java/time/Duration"]; ms_locks := []; ms_frames := ms_frames s |}
  end.
Definition duration_positive (seconds nanos : Z) : option Z :=
  match duration_start seconds nanos with
  | Some s => int_result (mrun bug_p bug_mdl 2000 s)
  | None => None end.

(** Duration(-1 second, 999999999 nanos) denotes exactly -1 nanosecond. *)
Theorem negative_nanosecond_is_reported_positive :
  (-1 * 1000000000 + 999999999 = -1) /\
  duration_positive (-1) 999999999 = Some 1.
Proof. vm_compute. auto. Qed.

Theorem duration_controls :
  duration_positive (-1) 0 = Some 0 /\
  duration_positive 0 0 = Some 0 /\
  duration_positive 0 1 = Some 1 /\
  duration_positive 1 0 = Some 1.
Proof. vm_compute. auto. Qed.

Print Assumptions filter_remove_wrong_element.
Print Assumptions filter_remove_before_next.
Print Assumptions negative_nanosecond_is_reported_positive.
Print Assumptions duration_controls.
