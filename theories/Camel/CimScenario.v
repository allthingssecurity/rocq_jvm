(** * camel-util CaseInsensitiveMap: put/remove/get on the real bytecode, main vs fix.

    The program is the real [CaseInsensitiveMap.class] of main (36bebb520a63) and of
    the fix branch camel-util-case-insensitive-map-removed-slots (27aeb4f860d9), the
    java.util model classes it needs ([AbstractMap], [Map]: Track B's clean-room models),
    and our test driver [CimScenario] (harness/camel/cim/.../CimScenario.java):
    - [churn(n)]: [put("h", i); remove("H")] n times; returns the map;
    - [run(seed, nops)]: a pseudo-random sequence of put/remove/get/containsKey on 4
      keys, each used in two case variants ("a"/"A", "Bb"/"bB", "Content-Type"/
      "CONTENT-type", "x-é"/"X-É"), checked step by step against a reference map
      (the result of every call and the size); returns the map, or null at the
      first difference.
    The slot capacity is the length of the map's private [keys] array, read from the
    machine's heap after the run ([slot_cap]).

    Computed in the kernel ([vm_compute]) on the machine of [JVM.Core.Machine]:
    - [main_churn_grows]: on main the slot capacity grows with the number of
      put/remove pairs of a single key (13, 19, 28, 63 after 13, 14, 20, 50 pairs):
      memory is never reclaimed for removed keys (the defect the fix addresses);
    - [fix_churn_bounded]: on the fix it stays 13 for every n <= 64;
    - [fix_runs] / [main_runs]: both behave as a map (every result and size
      agrees with the reference) on the listed random runs; the fix keeps 13 slots,
      main does not.
    The unbounded statement (every sequence of operations) is the next step. *)

From Stdlib Require Import ZArith String List Bool.
From JVM.Core Require Import Int Instr Desc Semantics Machine.
From JVM.Loader Require Import ClassFile.
From JVM.Jdk Require Import Strings Jdk.
From JVM.Camel Require Import CimProg.
Import ListNotations.
Open Scope Z_scope.

(** The length of the [keys] array of the map a run returned; [None] if the run did not
    return a CaseInsensitiveMap (null, exception, stuck, out of fuel). *)
Definition slot_cap (r : mresult) : option Z :=
  match r with
  | MRValue (Some (VRef l)) s =>
      match ms_heap s l with
      | Some (OObj c fs) =>
          if String.eqb c CIM then
            match assoc "keys" fs with
            | Some (VRef a) => match ms_heap s a with Some (OArr _ es) => Some (Z.of_nat (length es)) | _ => None end
            | _ => None
            end
          else None
      | _ => None
      end
  | _ => None
  end.

Definition churn (p : program) (n : Z) : option Z :=
  slot_cap (call_static p (jdk_model p env) 2000000 SCEN "churn" "(I)Lorg/apache/camel/util/CaseInsensitiveMap;" [VInt n]).
Definition run (p : program) (seed nops : Z) : option Z :=
  slot_cap (call_static p (jdk_model p env) 2000000 SCEN "run" "(II)Lorg/apache/camel/util/CaseInsensitiveMap;" [VInt seed; VInt nops]).

Theorem main_churn_grows :
  map (churn main_prog) [12; 13; 14; 20; 50] = [Some 13; Some 13; Some 19; Some 28; Some 63].
Proof. vm_compute. reflexivity. Qed.

Definition upto (n : nat) : list Z := map Z.of_nat (seq 0 n).

Theorem fix_churn_bounded : forallb (fun n => match churn fix_prog n with Some 13 => true | _ => false end) (upto 65) = true.
Proof. vm_compute. reflexivity. Qed.

(** 40 random runs of 100 operations each (seeds 0..39): both versions behave as a map
    (otherwise [run] returns null and [slot_cap] is [None]); main holds up to 28 slots for at
    most 4 keys, the fix 13. *)
Theorem main_runs : map (fun seed => run main_prog seed 100) (upto 40) =
  map Some [28;19;19;28;19;19;28;19;13;19;19;19;19;28;19;19;19;28;19;28;19;19;19;28;19;19;19;19;28;19;19;19;28;19;19;19;28;19;19;19].
Proof. vm_compute. reflexivity. Qed.

Theorem fix_runs : forallb (fun seed => match run fix_prog seed 100 with Some 13 => true | _ => false end) (upto 40) = true.
Proof. vm_compute. reflexivity. Qed.
