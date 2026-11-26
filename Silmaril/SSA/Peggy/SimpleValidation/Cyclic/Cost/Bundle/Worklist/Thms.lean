module

public import Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Defs
public import Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Thms
import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Worklist.Thms

public section

namespace Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist

open PEG
open PEG.Simple (Exec)
open RVSDG (Tuple)
open EPEG.Saturation
open EPEG.Saturation.Extension

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params rest : List (Ty Data)} {result : Ty Data}
variable [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
variable {zero : P [] .count} {fuel : Nat}
variable {source : Extension.Output P params (result :: rest) 1}

theorem CheckedReceipt.fixed (receipt : CheckedReceipt zero fuel source)
    (stop : receipt.report.stop = .fixed) : Dedup.Worklist.Fixed zero receipt.endpoint :=
  Dedup.Worklist.check_fixed receipt.checked stop

theorem CheckedReceipt.exhausted (receipt : CheckedReceipt zero fuel source)
    (stop : receipt.report.stop = .exhausted) :
    receipt.report.sites.length = fuel ∧ ¬ Dedup.Worklist.Fixed zero receipt.endpoint :=
  Dedup.Worklist.check_exhausted receipt.checked stop

/-- The minimum is relative to this pool and the exact replayed
partition, independently of the receipt's stop reason. -/
theorem CheckedReceipt.select_min (receipt : CheckedReceipt zero fuel source)
    {cost : Candidate receipt.endpoint.2.graph → Nat}
    {pool : List (Candidate receipt.endpoint.2.graph)}
    {chosen : Bundle.Accepted receipt.endpoint.2.graph receipt.endpoint.2.classes}
    (found : receipt.select cost pool = some chosen) {other : Candidate receipt.endpoint.2.graph}
    (member : other ∈ pool) (admitted : (Bundle.check receipt.endpoint.2.classes other).isSome = true) :
    cost chosen.candidate ≤ cost other :=
  Bundle.select_min found member admitted

variable {m : Interpretation.{u,v,w} P} {input : Tuple m.Value params}

theorem CheckedReceipt.preserves (receipt : CheckedReceipt zero fuel source)
    (zeroLaw : m.run zero .nil = some ⟨0⟩) : Dedup.Preserves m input source receipt.endpoint :=
  Dedup.Worklist.check_sound receipt.checked zeroLaw

/-- Relate the chosen graph directly to the input of the worklist.
The equality includes bottom at each ordered result. -/
theorem CheckedReceipt.observe_eq (receipt : CheckedReceipt zero fuel source)
    (a : Bundle.Accepted receipt.endpoint.2.graph receipt.endpoint.2.classes)
    (wf : WellFounded source.2.graph.Demand)
    (valid : source.2.classes.Valid (source.2.graph.denote m input wf))
    (zeroLaw : m.run zero .nil = some ⟨0⟩) (idx : Index 1) :
    source.2.graph.observe m (source.2.graph.denote m input wf) idx =
      a.candidate.graph.observe m (a.candidate.graph.denote m input a.reversion.demandWellFounded) idx := by
  obtain ⟨after, classes, observed⟩ := receipt.preserves zeroLaw wf valid
  exact (observed idx).symm.trans (a.observe_eq after classes idx)

/-- Every successful emitted execution realizes the original ordered
Figure 11 observation, even after an exhausted worklist prefix. -/
theorem CheckedReceipt.observe_of_exec (receipt : CheckedReceipt zero fuel source)
    (a : Bundle.Accepted receipt.endpoint.2.graph receipt.endpoint.2.classes)
    (wf : WellFounded source.2.graph.Demand)
    (valid : source.2.classes.Valid (source.2.graph.denote m input wf))
    (zeroLaw : m.run zero .nil = some ⟨0⟩)
    (neg : ∀ b : Bool, m.run a.reversion.scalar.descriptor.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (idx : Index 1) {output : Tuple m.Value (result :: rest)}
    (ran : Exec m a.output input (some output)) :
    source.2.graph.observe m (source.2.graph.denote m input wf) idx = output.map (fun _ => some) := by
  obtain ⟨_, _, observed⟩ := a.reversion.firstExit_of_exec neg idx ran
  exact (receipt.observe_eq a wf valid zeroLaw idx).trans observed

/-- Full guard and update totality are needed for the converse. -/
theorem CheckedReceipt.exec_iff_observe (receipt : CheckedReceipt zero fuel source)
    (a : Bundle.Accepted receipt.endpoint.2.graph receipt.endpoint.2.classes)
    (wf : WellFounded source.2.graph.Demand)
    (valid : source.2.classes.Valid (source.2.graph.denote m input wf))
    (zeroLaw : m.run zero .nil = some ⟨0⟩) (total : a.reversion.scalar.Total m)
    (neg : ∀ b : Bool, m.run a.reversion.scalar.descriptor.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (idx : Index 1) (output : Tuple m.Value (result :: rest)) :
    Exec m a.output input (some output) ↔
      source.2.graph.observe m (source.2.graph.denote m input wf) idx = output.map (fun _ => some) :=
  (a.reversion.exec_iff_observe total neg idx output).trans
    (congrArg (· = output.map (fun _ => some)) (receipt.observe_eq a wf valid zeroLaw idx).symm).to_iff

end Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist
