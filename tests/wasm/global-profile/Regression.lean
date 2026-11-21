module

import Silmaril.Wasm.Execution.Core.GlobalProfile.Thms
import Silmaril.Wasm.Execution.Core.Entry.Determinism.Thms
import Silmaril.Wasm.Execution.Core.Entry.Thms

open Silmaril.Wasm Silmaril.Wasm.Numerics Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Execution.Core.GlobalProfile Silmaril.Wasm.SingleThreaded.Det Silmaril.Semantics.Operational

private def inc : Code .var [] [.i32] :=
  .get (.const 2 (.bin .add (.set (.get .done))))

private def incAndTrap : Code .var [] [.i32] :=
  .get (.const 2 (.bin .add (.set (.get (.const 0 (.bin (.div .unsigned) .done))))))

private def readOnly : Code .const [] [.i32] := .get (.const 3 (.bin .mul .done))

private def readOnlyProgram : Program .const [.i32] := ⟨14, readOnly⟩

example (P : Profile) : (opSem P .const [.i32]).initial readOnlyProgram (readOnly.start .nil 14) := rfl

example (P : Profile) : (opSem P .const [.i32]).semantics.toOpSem.May (readOnly.start .nil 14)
    (.returned (.ok [.i32 42])) :=
  (safe_and_may (P := P) readOnly .nil 14).2 _ |>.mpr rfl

example (P : Profile) : Entry.Finishes P noHost (inc.start .nil 40)
    (config .var 42 [(Val.i32 42).toAdmin]) (.values [.i32 42]) :=
  eval_finishes inc .nil 40

example (P : Profile) : Entry.Finishes P noHost (incAndTrap.start .nil 40)
    (config .var 42 [.trap]) .trap :=
  eval_finishes incAndTrap .nil 40

example (P : Profile) (final : Config Empty) (result : Result)
    (run : Entry.Finishes P noHost (incAndTrap.start .nil 40) final result) :
    final = config .var 42 [.trap] ∧ result = .trap :=
  (finishes_iff incAndTrap .nil 40 final result).mp run

example (P : Profile) : let sem := (opSem P .var [.i32]).semantics
    sem.SafeAt (incAndTrap.start .nil 40) ∧ sem.toOpSem.May (incAndTrap.start .nil 40) .trap :=
  ⟨(safe_and_may incAndTrap .nil 40).1, (safe_and_may incAndTrap .nil 40).2 _ |>.mpr rfl⟩

example (P : Profile) : (Entry.ordinary P noHost).ResultDetAt (inc.start .nil 40) := by
  apply OpSem.resultDetAt_iff.mpr
  intro left right seenLeft seenRight
  obtain ⟨finalLeft, resultLeft, runLeft, rfl⟩ := Entry.ordinary_may.mp seenLeft
  obtain ⟨finalRight, resultRight, runRight, rfl⟩ := Entry.ordinary_may.mp seenRight
  rw [(finishes_iff inc .nil 40 finalLeft resultLeft).mp runLeft |>.2,
    (finishes_iff inc .nil 40 finalRight resultRight).mp runRight |>.2]

example (P : Profile) : ¬ Diverges P noHost (incAndTrap.start .nil 40) := not_diverges incAndTrap .nil 40

example : True := by
  fail_if_success have _immutableWrite : Code .const [.i32] [] := .set .done
  trivial

/-- Raw Core reduction does not check mutability; this is why admission
and the actual typing policy matter. It is not an allowed typed tape. -/
example (P : Profile) : Step P noHost (config .const 40 [(Val.i32 42).toAdmin, set]) (config .const 42 []) :=
  .variable (.globalSet (a := 0) (g := global .const 40) rfl)

#print axioms start_typed
#print axioms eval_finishes
#print axioms finishes_iff
#print axioms safe_and_may
#print axioms not_diverges
