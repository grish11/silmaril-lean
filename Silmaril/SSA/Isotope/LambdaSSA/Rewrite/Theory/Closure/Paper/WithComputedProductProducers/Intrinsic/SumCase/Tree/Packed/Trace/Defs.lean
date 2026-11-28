module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.SumCase.Tree.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Sequence.Model.Defs

/-! # A selected nested case over the ordered trace signature -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic.CaseTree.Trace

open Silmaril
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Sequence (signature Op)

local instance : HasTy signature.Instr (Ty Empty) := signature.hasTy

abbrev Flag : (Ty Empty) := coprod unit unit
abbrev Input : (Ty Empty) := product Flag Flag
abbrev Exits : LCtx (Ty Empty) := [unit, unit]

/-- Emit once before reading the carried flag. The trace signature's
primitive itself returns unit. -/
def report {X : (Ty Empty)} (bit : Bool) (flag : Term signature.Instr X Flag) : Term signature.Instr X Flag :=
  .seq (.pair (.call (show signature.Instr from Op.emit bit) .unit) flag) (.snd unit Flag)

/-- The outer case observes the first flag. The inner case observes the
retained second flag and can return through either ordered exit. -/
def nested : CaseTree signature.Instr Input Exits :=
  .case unit unit (report true (.fst Flag Flag))
    (.case unit unit (report false (.seq (.fst Input unit) (.snd Flag Flag)))
      (.exit 0 rfl (.returned .unit))
      (.exit 1 rfl (.returned .unit)))
    (.exit 0 rfl (.returned .unit))

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic.CaseTree.Trace
