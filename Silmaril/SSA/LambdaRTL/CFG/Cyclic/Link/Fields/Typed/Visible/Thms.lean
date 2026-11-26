module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Defs
public import Silmaril.Semantics.ITree.Trace.Finite.Thms
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Named
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Interface

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Program

open Silmaril.Elgot.ITree (TraceLE eq_iff_traceLE)
open Silmaril.Elgot.ITree.Finite (evaluate)

variable {F : Type} {signature : PrimitiveSignature F} {a b : Nat}
  {inputs : Fin a → PacketType} {outputs : Fin b → PacketType}
  (program : Program signature inputs outputs)

/-- The named runner observes the exact typed reply continuations. Its
returned label is numbered in the ordered, typed exit interface. -/
theorem observe_eq (input : Fin a) (packet : Denote (inputs input)) :
    program.observe input packet =
      (evaluate program.step (program.start input packet) >>= fun r => pure (renderResult r)) :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.observe_eq program input packet

theorem refinementAt?_iff [DecidableEq F] (right : Program signature inputs outputs)
    (input : Fin a) (packet : Denote (inputs input)) :
    program.refinementAt? right input packet = true ↔
      TraceLE (program.observe input packet) (right.observe input packet) :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.compare_at program right input packet

/-- Mutual finite weak trace inclusion decides equality in the deterministic
weak tree model of the named runner. Pending requests remain observable
even when their reply type is empty. -/
theorem weakEqAt?_iff [DecidableEq F] (right : Program signature inputs outputs)
    (input : Fin a) (packet : Denote (inputs input)) :
    program.weakEqAt? right input packet = true ↔
      program.observe input packet = right.observe input packet := by
  simp only [weakEqAt?, Bool.and_eq_true, refinementAt?_iff, eq_iff_traceLE]

theorem firstMismatch?_none_iff [DecidableEq F] (right : Program signature inputs outputs) :
    program.firstMismatch? right = none ↔
      ∀ input packet, program.observe input packet = right.observe input packet := by
  rw [Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.mismatch_none]
  simp only [weakEqAt?_iff]

theorem firstMismatch?_sound [DecidableEq F] {right : Program signature inputs outputs}
    {p : PacketAt inputs} (found : program.firstMismatch? right = some p) :
    program.observe p.1 p.2 ≠ right.observe p.1 p.2 :=
  mt (program.weakEqAt?_iff right p.1 p.2).mpr
    (Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.mismatch_some found)

theorem weakEq?_iff [DecidableEq F] (right : Program signature inputs outputs) :
    program.weakEq? right = true ↔
      ∀ input packet, program.observe input packet = right.observe input packet := by
  rw [weakEq?, Option.isNone_iff_eq_none, firstMismatch?_none_iff]

/-- Exact finite weak trace inclusion over every typed packet at every
public input. The programs share their signature and ordered external
interfaces. Their private label types and packet shapes may differ. -/
theorem refinement?_iff [DecidableEq F] (right : Program signature inputs outputs) :
    program.refinement? right = true ↔
      ∀ input packet, TraceLE (program.observe input packet) (right.observe input packet) := by
  simp [refinement?, refinementAt?_iff]

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Program
