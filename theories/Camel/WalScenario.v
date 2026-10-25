(** * camel-wal TransactionLog as a whole class: add + update, on the real bytecode.

    The program is the real class files of camel-wal (TransactionLog, its
    nested LayerInfo / EntryContainer, LogEntry, LogEntry.EntryState), main
    (36bebb520a63) and fix (e72996b974ad), plus our test driver
    [WalScenario.check(cap, n, k)] (harness/camel/wal-*/.../WalScenario.java):
    a log of capacity [cap] gets [n] entries (entry i has keyMetadata i), the
    k-th is updated to FAILED through the LayerInfo that [add] returned for it,
    and the driver returns the keyMetadata of the entry that is FAILED
    afterwards, or -1.  Contract (CAMEL-26088): the result is k if entry k is
    still in the ring buffer (n - cap <= k), else -1.

    Everything runs in the machine of [JVM.Core.Machine] with the JDK models of
    [JVM.Jdk.Jdk] (here: Object.<init>, Enum, slf4j loggers); computed by the
    kernel's [vm_compute].
    - [main_marks_newer_entry]: on main, updating entry 2 of 10 in a log of
      capacity 3 marks entry 8 (a newer entry in the same slot).
    - [main_rejects_live_entry]: on main, entry 5 of 9 (capacity 4) is live but
      is not updated.
    - [fix_bounded]: the fix meets the contract for every capacity 1..4, every
      n <= 12 and every k < n, with slf4j debug logging disabled and enabled.
    The unbounded statement for the whole class needs symbolic heap reasoning
    (next step); for the predicate itself it is [WalCanUpdate.fix_correct]. *)

From Stdlib Require Import ZArith String List Bool.
From JVM.Core Require Import Int Instr Desc Semantics Machine.
From JVM.Loader Require Import ClassFile.
From JVM.Jdk Require Import Strings Jdk.
From JVM.Classes Require WalScenMain WalScenFix.
Import ListNotations.
Open Scope Z_scope.

(** ASCII-only Unicode environment (unused by this program, which has no text). *)
Definition ascii_uenv : uenv := {|
  u_upper := ascii_upper; u_lower := ascii_lower;
  u_digit := fun c r => if (48 <=? c) && (c <=? 57) && (10 <=? r) then c - 48 else -1;
  u_is_whitespace := fun c => (c =? 32) || ((9 <=? c) && (c <=? 13)) || ((28 <=? c) && (c <=? 31));
  u_is_letter := fun c => ((65 <=? c) && (c <=? 90)) || ((97 <=? c) && (c <=? 122));
  u_is_digit := fun c => (48 <=? c) && (c <=? 57);
  u_is_upper := fun c => (65 <=? c) && (c <=? 90);
  u_is_lower := fun c => (97 <=? c) && (c <=? 122) |}.

Definition env (log : bool) : jenv := {| j_u := ascii_uenv; j_log_enabled := fun _ => log; j_ihash := fun l => l |}.

Definition result_int (r : mresult) : option Z :=
  match r with MRValue (Some (VInt z)) _ => Some z | _ => None end.

Definition check (files : list (list Z)) (log : bool) (cap n k : Z) : option Z :=
  match load_program files with
  | Some p => result_int (call_static p (jdk_model p (env log)) 200000
                            "org/apache/camel/component/wal/WalScenario" "check" "(III)I"
                            [VInt cap; VInt n; VInt k])
  | None => None
  end.

Definition contract (cap n k : Z) : Z := if n - cap <=? k then k else -1.

Theorem main_marks_newer_entry : check WalScenMain.files false 3 10 2 = Some 8.
Proof. vm_compute. reflexivity. Qed.

Theorem main_rejects_live_entry : contract 4 9 5 = 5 /\ check WalScenMain.files false 4 9 5 = Some (-1).
Proof. vm_compute. auto. Qed.

Definition all_ok (files : list (list Z)) (log : bool) (maxcap maxn : nat) : bool :=
  forallb (fun cap =>
    forallb (fun n =>
      forallb (fun k => match check files log cap n k with
                        | Some r => Z.eqb r (contract cap n k)
                        | None => false
                        end)
              (map Z.of_nat (seq 0 (Z.to_nat n))))
      (map Z.of_nat (seq 0 (S maxn))))
    (map Z.of_nat (seq 1 maxcap)).

Theorem fix_bounded : all_ok WalScenFix.files false 4 12 = true /\ all_ok WalScenFix.files true 4 12 = true.
Proof. split; vm_compute; reflexivity. Qed.

Theorem main_bounded_fails : all_ok WalScenMain.files false 4 12 = false.
Proof. vm_compute. reflexivity. Qed.
