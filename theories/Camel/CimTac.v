(** Tactics for symbolic execution of the CaseInsensitiveMap bytecode on states whose
    frames are concrete and whose heap is a chain of updates of a variable heap. *)
From Stdlib Require Import ZArith String List Bool Lia.
From JVM.Core Require Import Int Instr Desc Semantics Machine Logic.

Ltac use_hyps :=
  repeat match goal with
  | H : ?a = ?b |- context [?a] => progress rewrite H
  end.

Ltac nz := match goal with |- returns ?p ?m ?S ?v ?P =>
  let S1 := eval unfold with_frames, set_frame, set_resume, alloc in S in
  let S2 := eval cbn [ms_heap ms_next ms_statics ms_inited ms_locks ms_frames cf_class cf_method cf_code
                      cf_rt cf_frame cf_resume cf_clinit f_pc f_stack f_locals fst snd narrow_store] in S1 in
  change (returns p m S2 v P) end.

Ltac lstep := eapply returns_step;
  [ eapply mstep_local; [ reflexivity | reflexivity | reflexivity
                        | cbn -[wrap i2c Z.mul iinc cat2 upd Z.pow Z.modulo]; use_hyps; cbn -[wrap i2c Z.mul iinc upd Z.pow Z.modulo]; reflexivity
                        | cbn -[cat2 slots upd]; use_hyps; reflexivity ]
  | try nz ].

Ltac neq := first [ assumption | apply not_eq_sym; assumption | lia ].
Ltac hp := cbn [ms_heap ms_statics ms_inited];
  repeat first [ rewrite upd_same | rewrite upd_other by neq ];
  first [ eassumption | reflexivity ].

Ltac GET := eapply returns_step;
  [ eapply mstep_getfield; [ reflexivity | reflexivity | reflexivity | hp | first [ reflexivity | eassumption ] | reflexivity ] | try nz ].
Ltac PUT := eapply returns_step;
  [ eapply mstep_putfield; [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | hp
                           | reflexivity | reflexivity ] | try nz ].
Ltac RET := eapply returns_step;
  [ eapply mstep_return_to; [ reflexivity | reflexivity | reflexivity | reflexivity | cbn; reflexivity | reflexivity ]
  | try nz ].
Ltac ALEN := eapply returns_step;
  [ eapply mstep_arraylength; [ reflexivity | reflexivity | reflexivity | hp | reflexivity ] | try nz ].
