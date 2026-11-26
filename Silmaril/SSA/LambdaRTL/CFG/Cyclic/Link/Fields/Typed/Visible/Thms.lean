module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Defs
public import Silmaril.Semantics.ITree.Trace.Finite.Thms
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Named

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Program

open Silmaril.Elgot.ITree (TraceLE)
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

/-- Exact finite weak trace inclusion over every typed packet at every
public input. The programs share their signature and ordered external
interfaces. Their private label types and packet shapes may differ. -/
theorem refinement?_iff [DecidableEq F] (right : Program signature inputs outputs) :
    program.refinement? right = true ↔
      ∀ input packet, TraceLE (program.observe input packet) (right.observe input packet) := by
  simp [refinement?, refinementAt?_iff]

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Program
