module

public import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Worklist.Combined.Defs
public import Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Defs

/-! # Ordered selection from checked two-rule receipts -/

@[expose] public section

namespace Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Combined

open PEG
open EPEG.Saturation
open EPEG.Saturation.Extension

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params rest : List (Ty Data)} {result : Ty Data}
variable [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]

abbrev CheckedReceipt (ops : Extension.Worklist.Combined.Ops P) (fuel : Nat)
    (source : Output P params (result :: rest) 1) :=
  CheckedReplay (Extension.Worklist.Combined.driver ops) fuel source

def check (ops : Extension.Worklist.Combined.Ops P) (fuel : Nat)
    (source : Output P params (result :: rest) 1)
    (report : Extension.Worklist.Report Extension.Worklist.Combined.Action) :
    Option (CheckedReceipt ops fuel source) :=
  checkWith (Extension.Worklist.Combined.driver ops) fuel source report

end Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Combined
