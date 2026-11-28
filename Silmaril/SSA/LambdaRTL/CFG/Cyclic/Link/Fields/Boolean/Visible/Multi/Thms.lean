module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.Multi.Defs
public import Silmaril.Semantics.ITree.Trace.Finite.Silence.Thms
import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Thms
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.Multi.Named

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.Multi.Program

open Silmaril.Elgot.ITree (TraceLE ExchangePath SilentAfter TraceLEWithSilence
  traceLEWithSilence_iff_mutual silentAfter_bind_pure_iff)
open Silmaril.Elgot.ITree.Finite (Event evaluate)

variable {F : Type} {a b n : Nat} (program : Program F a b n)

/-- The finite table and the actual named runner see the same requests,
typed replies, and returned packets, with public ports numbered. -/
theorem observe_eq (input : Fin a) (packet : Packet n) :
    program.observe input packet =
      (evaluate program.step (program.start input packet) >>= fun r => pure (renderResult r)) :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.Multi.observe_eq program input packet

theorem refinementAt?_iff [DecidableEq F] (right : Program F a b n) (input : Fin a) (packet : Packet n) :
    program.refinementAt? right input packet = true ↔
      TraceLE (program.observe input packet) (right.observe input packet) :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.Multi.compare_at program right input packet

/-- Exact finite weak trace inclusion at every public input and every
well-formed Boolean packet of the common width. -/
theorem refinement?_iff [DecidableEq F] (right : Program F a b n) :
    program.refinement? right = true ↔ ∀ input packet, TraceLE (program.observe input packet) (right.observe input packet) := by
  simp [refinement?, List.all_eq_true, Boolean.mem_packets, refinementAt?_iff]

theorem silentAfter?_iff [DecidableEq F] (input : Fin a) (packet : Packet n)
    (path : ExchangePath (Event (F × Bool))) :
    program.silentAfter? input packet path = true ↔ SilentAfter (program.observe input packet) path := by
  rw [silentAfter?, observe_eq, silentAfter_bind_pure_iff]
  exact Silmaril.Elgot.ITree.Finite.silentAfter?_iff program.step program.states program.mem_states _ path

theorem refinementAtWithSilence?_iff [DecidableEq F] (right : Program F a b n) (input : Fin a) (packet : Packet n) :
    program.refinementAtWithSilence? right input packet = true ↔
      TraceLEWithSilence (program.observe input packet) (right.observe input packet) := by
  simp only [refinementAtWithSilence?, Bool.and_eq_true, refinementAt?_iff, traceLEWithSilence_iff_mutual]

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.Multi.Program
