---------------------------- MODULE BoundedCounter ----------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC, Apalache, Variants

VARIABLE
  (*
    @type: Int;
  *)
  n

(*
  @type: (() => Bool);
*)
step == n < 2 /\ n' := n + 1

(*
  @type: (() => Bool);
*)
init == n = 0

(*
  @type: (() => Bool);
*)
q_init == init

(*
  @type: (() => Bool);
*)
q_step == step

================================================================================
