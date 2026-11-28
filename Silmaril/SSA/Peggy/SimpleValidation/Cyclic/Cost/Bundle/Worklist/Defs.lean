module

public import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Worklist.Defs
public import Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Defs

/-! # Ordered cost selection after checked worklist replay -/

@[expose] public section

namespace Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist

open PEG
open EPEG.Saturation
open EPEG.Saturation.Extension

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params rest : List (Ty Data)} {result : Ty Data}
variable {Action : Type w}

/-- The driver reconstructs the endpoint from the original source and
the report. The endpoint's table and classes stay paired. -/
structure CheckedReplay
    (driver : Extension.Worklist.Driver (Extension.Output P params (result :: rest) 1) Action)
    (fuel : Nat) (source : Extension.Output P params (result :: rest) 1) where
  report : Extension.Worklist.Report Action
  endpoint : Extension.Output P params (result :: rest) 1
  checked : driver.check fuel source report = some endpoint

def checkWith
    (driver : Extension.Worklist.Driver (Extension.Output P params (result :: rest) 1) Action)
    (fuel : Nat) (source : Extension.Output P params (result :: rest) 1)
    (report : Extension.Worklist.Report Action) : Option (CheckedReplay driver fuel source) :=
  match replay : driver.check fuel source report with
  | none => none
  | some endpoint => some ⟨report, endpoint, replay⟩

variable {driver : Extension.Worklist.Driver (Extension.Output P params (result :: rest) 1) Action}
variable {fuel : Nat} {source : Extension.Output P params (result :: rest) 1}
variable [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]

/-- Supply candidates for the replayed table. Both checked stop statuses
are eligible for cost selection. -/
abbrev CheckedReplay.select (receipt : CheckedReplay driver fuel source)
    (cost : Candidate receipt.endpoint.2.graph → Nat)
    (pool : List (Candidate receipt.endpoint.2.graph)) :
    Option (Bundle.Accepted receipt.endpoint.2.graph receipt.endpoint.2.classes) :=
  Bundle.select receipt.endpoint.2.classes cost pool

abbrev CheckedReceipt (zero : P [] .count) (fuel : Nat)
    (source : Extension.Output P params (result :: rest) 1) :=
  CheckedReplay (Dedup.Worklist.driver zero) fuel source

def check (zero : P [] .count) (fuel : Nat)
    (source : Extension.Output P params (result :: rest) 1) (report : Dedup.Worklist.Report) :
    Option (CheckedReceipt zero fuel source) :=
  checkWith (Dedup.Worklist.driver zero) fuel source report

variable {zero : P [] .count}

/-- The numeric zero-sample entry point uses the shared selector. -/
abbrev CheckedReceipt.select (receipt : CheckedReceipt zero fuel source)
    (cost : Candidate receipt.endpoint.2.graph → Nat)
    (pool : List (Candidate receipt.endpoint.2.graph)) :
    Option (Bundle.Accepted receipt.endpoint.2.graph receipt.endpoint.2.classes) :=
  CheckedReplay.select receipt cost pool

end Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist
