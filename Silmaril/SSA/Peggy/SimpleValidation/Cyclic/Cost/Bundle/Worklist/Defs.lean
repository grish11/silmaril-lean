module

public import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Worklist.Defs
public import Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Defs

/-! # Ordered cost selection after checked zero-sample replay -/

@[expose] public section

namespace Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist

open PEG
open EPEG.Saturation
open EPEG.Saturation.Extension

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params rest : List (Ty Data)} {result : Ty Data}
variable [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]

/-- The endpoint comes from independently replaying the report against
the original input. Its row table and classes stay paired. -/
structure CheckedReceipt (zero : P [] .count) (fuel : Nat)
    (source : Extension.Output P params (result :: rest) 1) where
  report : Dedup.Worklist.Report
  endpoint : Extension.Output P params (result :: rest) 1
  checked : Dedup.Worklist.check zero fuel source report = some endpoint

def check (zero : P [] .count) (fuel : Nat)
    (source : Extension.Output P params (result :: rest) 1) (report : Dedup.Worklist.Report) :
    Option (CheckedReceipt zero fuel source) :=
  match replay : Dedup.Worklist.check zero fuel source report with
  | none => none
  | some endpoint => some ⟨report, endpoint, replay⟩

variable {zero : P [] .count} {fuel : Nat}
variable {source : Extension.Output P params (result :: rest) 1}

/-- Supply candidates for the replayed table. Both stop statuses are
eligible. Cost selection neither changes nor tests the stop status. -/
abbrev CheckedReceipt.select (receipt : CheckedReceipt zero fuel source)
    (cost : Candidate receipt.endpoint.2.graph → Nat)
    (pool : List (Candidate receipt.endpoint.2.graph)) :
    Option (Bundle.Accepted receipt.endpoint.2.graph receipt.endpoint.2.classes) :=
  Bundle.select receipt.endpoint.2.classes cost pool

end Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist
