(** * Tactics for symbolic execution of loaded bytecode. *)
From Stdlib Require Import ZArith Bool Lia String.
From JVM.Core Require Import Int Instr Desc Semantics.

(** Turn boolean comparison facts into linear arithmetic facts. *)
Ltac bool_to_prop :=
  repeat match goal with
  | H : negb _ = true |- _ => apply negb_true_iff in H
  | H : negb _ = false |- _ => apply negb_false_iff in H
  | H : (_ =? _)%Z = true |- _ => apply Z.eqb_eq in H
  | H : (_ =? _)%Z = false |- _ => apply Z.eqb_neq in H
  | H : (_ <? _)%Z = true |- _ => apply Z.ltb_lt in H
  | H : (_ <? _)%Z = false |- _ => apply Z.ltb_ge in H
  | H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H
  | H : (_ <=? _)%Z = false |- _ => apply Z.leb_gt in H
  | H : (_ && _) = true |- _ => apply andb_true_iff in H; destruct H
  | H : (_ || _) = false |- _ => apply orb_false_iff in H; destruct H
  | H : (_ && _) = false |- _ => apply andb_false_iff in H; destruct H
  | H : (_ || _) = true |- _ => apply orb_true_iff in H; destruct H
  end.

(** Destruct the innermost boolean test of the goal. *)
Ltac split_if :=
  match goal with
  | |- context [if ?b then _ else _] =>
      lazymatch b with
      | context [if _ then _ else _] => fail
      | _ => destruct b eqn:?
      end
  end.

(** Symbolic execution: reduce the interpreter with [cbn] (keeping the
    integer range test and [wrap] folded), split on every branch condition. *)
Ltac symex :=
  repeat (cbn -[in_rangeb wrap]; try split_if).

Ltac close_arith :=
  bool_to_prop; unfold in_int, in_range, INT_MAX, INT_MIN in *; simpl in *; lia.

(** Finish a symbolic-execution branch whose goal is an equation between
    results: split the remaining tests on the right-hand side, then either
    the two sides are syntactically equal or the branch conditions are
    contradictory in linear integer arithmetic. *)
Ltac finish_branch :=
  repeat split_if; first [reflexivity | exfalso; close_arith].
