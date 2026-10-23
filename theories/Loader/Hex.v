(** * Hex strings to bytes (used by the generated class-file modules). *)
From Stdlib Require Import String Ascii ZArith List Bool.
Open Scope bool_scope.
Open Scope Z_scope.

Definition hexdigit (c : ascii) : Z :=
  let n := Z.of_nat (nat_of_ascii c) in
  if (48 <=? n) && (n <=? 57) then n - 48          (* 0-9 *)
  else if (97 <=? n) && (n <=? 102) then n - 87    (* a-f *)
  else if (65 <=? n) && (n <=? 70) then n - 55     (* A-F *)
  else 0.

(** Malformed input (odd length, non-hex characters) is not rejected here;
    tools/check-dumps.sh checks that each dump is the exact hex of its file. *)
Fixpoint hex_to_bytes (s : string) : list Z :=
  match s with
  | String a (String b r) => (hexdigit a * 16 + hexdigit b) :: hex_to_bytes r
  | _ => nil
  end.

Example hex_ex : hex_to_bytes "cafeBABE00" = (202 :: 254 :: 186 :: 190 :: 0 :: nil).
Proof. reflexivity. Qed.
