module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.Defs
public import Silmaril.Semantics.ITree.Trace.Finite.Thms
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.Named

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.Program

open Silmaril.Elgot.ITree (TraceLE)
open Silmaril.Elgot.ITree.Finite (evaluate)

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

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.Program
