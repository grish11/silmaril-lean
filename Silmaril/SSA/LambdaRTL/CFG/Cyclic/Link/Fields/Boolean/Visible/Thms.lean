module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.Defs
public import Silmaril.Semantics.ITree.Trace.Finite.Silence.Thms
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.Named

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.Program

open Silmaril.Elgot.ITree (TraceLE ExchangePath SilentAfter TraceLEWithSilence
  traceLEWithSilence_iff_mutual silentAfter_bind_pure_iff)
open Silmaril.Elgot.ITree.Finite (Event evaluate)

variable {F : Type} {a b : Nat} (program : Program F a b)

/-- The finite table preserves the named runner's whole weak tree. Only the
returned port and packet are encoded. Requests carry the opcode and Boolean
argument, and both Boolean replies continue in the same runner. -/
theorem observe_eq (input : Fin a) (flag : Bool) :
    program.observe input flag =
      (evaluate program.step (program.start input flag) >>= fun r => pure (renderResult r)) :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.observe_eq program input flag

theorem refinementAt?_iff [DecidableEq F] (right : Program F a b) (input : Fin a) (flag : Bool) :
    program.refinementAt? right input flag = true ↔ TraceLE (program.observe input flag) (right.observe input flag) :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.compare_at program right input flag

/-- Exact finite-prefix trace inclusion at every supplied one-field Boolean
packet, including pending requests and terminating exit/payload observations. -/
theorem refinement?_iff [DecidableEq F] (right : Program F a b) :
    program.refinement? right = true ↔ ∀ input flag, TraceLE (program.observe input flag) (right.observe input flag) :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.compare_all program right

theorem silentAfter?_iff [DecidableEq F] (input : Fin a) (flag : Bool)
    (path : ExchangePath (Event (F × Bool))) :
    program.silentAfter? input flag path = true ↔ SilentAfter (program.observe input flag) path := by
  rw [silentAfter?, observe_eq, silentAfter_bind_pure_iff]
  exact Silmaril.Elgot.ITree.Finite.silentAfter?_iff program.step program.states program.mem_states _ path

theorem refinementAtWithSilence?_iff [DecidableEq F] (right : Program F a b) (input : Fin a) (flag : Bool) :
    program.refinementAtWithSilence? right input flag = true ↔
      TraceLEWithSilence (program.observe input flag) (right.observe input flag) := by
  simp only [refinementAtWithSilence?, Bool.and_eq_true, refinementAt?_iff, traceLEWithSilence_iff_mutual]

/-- Compare all entries and Boolean packets, preserving finite silent
endpoints in addition to pending requests and returns. -/
theorem refinementWithSilence?_iff [DecidableEq F] (right : Program F a b) :
    program.refinementWithSilence? right = true ↔
      ∀ input flag, TraceLEWithSilence (program.observe input flag) (right.observe input flag) := by
  simp only [refinementWithSilence?, Bool.and_eq_true, refinement?_iff, traceLEWithSilence_iff_mutual, forall_and]

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.Program
