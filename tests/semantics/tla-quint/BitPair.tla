-------------------------------- MODULE BitPair --------------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC, Apalache, Variants

VARIABLE
  (*
    @type: Int;
  *)
  x

VARIABLE
  (*
    @type: Int;
  *)
  y

(*
  @type: (() => Bool);
*)
init == x = 0 /\ y = 1

(*
  @type: (() => Bool);
*)
step ==
  \E flip \in { FALSE, TRUE }: x' := y /\ y' := (IF flip THEN 1 - x ELSE x)

(*
  @type: (() => Bool);
*)
q_init == init

(*
  @type: (() => Bool);
*)
q_step == step

================================================================================
