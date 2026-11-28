module

public import Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Combined.Defs
public import Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Thms
import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Worklist.Combined.Thms
import Silmaril.SSA.Peggy.Worked.EvalScale.Defs

public section

namespace Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Combined

open PEG
open PEG.Simple (Exec)
open EPEG.Saturation
open EPEG.Saturation.Extension
open Worked
open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params rest : List (Ty Data)} {result : Ty Data}
variable [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
variable {ops : Extension.Worklist.Combined.Ops P} {fuel : Nat}
variable {source : Output P params (result :: rest) 1}

theorem CheckedReceipt.fixed (receipt : CheckedReceipt ops fuel source)
    (stop : receipt.report.stop = .fixed) : Extension.Worklist.Combined.Fixed ops receipt.endpoint :=
  Extension.Worklist.Combined.check_fixed receipt.checked stop

theorem CheckedReceipt.exhausted (receipt : CheckedReceipt ops fuel source)
    (stop : receipt.report.stop = .exhausted) :
    receipt.report.sites.length = fuel ∧ ¬ Extension.Worklist.Combined.Fixed ops receipt.endpoint :=
  Extension.Worklist.Combined.check_exhausted receipt.checked stop

variable {m : Interpretation.{u,v,w} P} {input : Tuple m.Value params}

theorem CheckedReceipt.preserves (receipt : CheckedReceipt ops fuel source)
    (zeroLaw : m.run ops.zero .nil = some ⟨0⟩) (scaleLaw : EvalScale.Law m ops.factor ops.scale) :
    Dedup.Preserves m input source receipt.endpoint :=
  Extension.Worklist.Combined.check_sound receipt.checked zeroLaw scaleLaw

/-- A selected candidate has the original ordered partial observations
for either checked stop status. -/
theorem CheckedReceipt.observe_eq (receipt : CheckedReceipt ops fuel source)
    (a : Bundle.Accepted receipt.endpoint.2.graph receipt.endpoint.2.classes)
    (wf : WellFounded source.2.graph.Demand)
    (valid : source.2.classes.Valid (source.2.graph.denote m input wf))
    (zeroLaw : m.run ops.zero .nil = some ⟨0⟩) (scaleLaw : EvalScale.Law m ops.factor ops.scale)
    (idx : Index 1) :
    source.2.graph.observe m (source.2.graph.denote m input wf) idx =
      a.candidate.graph.observe m (a.candidate.graph.denote m input a.reversion.demandWellFounded) idx :=
  CheckedReplay.observe_eq_of_preserves receipt a (receipt.preserves zeroLaw scaleLaw) wf valid idx

theorem CheckedReceipt.observe_of_exec (receipt : CheckedReceipt ops fuel source)
    (a : Bundle.Accepted receipt.endpoint.2.graph receipt.endpoint.2.classes)
    (wf : WellFounded source.2.graph.Demand)
    (valid : source.2.classes.Valid (source.2.graph.denote m input wf))
    (zeroLaw : m.run ops.zero .nil = some ⟨0⟩) (scaleLaw : EvalScale.Law m ops.factor ops.scale)
    (neg : ∀ b : Bool, m.run a.reversion.scalar.descriptor.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (idx : Index 1) {output : Tuple m.Value (result :: rest)}
    (ran : Exec m a.output input (some output)) :
    source.2.graph.observe m (source.2.graph.denote m input wf) idx = output.map (fun _ => some) := by
  obtain ⟨_, _, observed⟩ := a.reversion.firstExit_of_exec neg idx ran
  exact (receipt.observe_eq a wf valid zeroLaw scaleLaw idx).trans observed

end Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Combined
