module

public import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Worklist.Combined.Defs
import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Worklist.Thms
import Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Worklist.Combined.Sound

public section

namespace Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Worklist.Combined

open PEG
open Worked
open RVSDG (Tuple)

universe u v x

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {l : Nat}
variable {ops : Ops P} {source target : Output P params results l}
variable {m : Interpretation.{u,v,x} P} {env : Tuple m.Value params}
variable [DecidableEq Data] [DecidableEq (P [.count, .count] .count)]

theorem checkCovered_iff {n : Nat} {g : Graph P params results n l} {site : Fin n}
    (found : EvalScale.Match g site ops.factor ops.scale) (classes : Classes n) :
    checkCovered found classes = true ↔
      ∃ rhs, checkRhs found rhs = true ∧ classes site = classes rhs := by
  simp only [checkCovered, List.any_eq_true, List.mem_finRange, true_and, Bool.and_eq_true, beq_iff_eq]

variable [DecidableEq (P [] .count)]

theorem run_checked (fuel : Nat) (s : Output P params results l) :
    (driver ops).check fuel s ((driver ops).run fuel s).report = some ((driver ops).run fuel s).state :=
  Driver.run_checked (fun hit => List.find?_some hit) fuel s

/-- Every address has both rule tags checked for closure. -/
theorem next_none_iff (s : Output P params results l) : (driver ops).next s = none ↔ Fixed ops s :=
  Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Worklist.Combined.next_none_iff s

theorem check_fixed {fuel : Nat} {report : Report Action}
    (hit : (driver ops).check fuel source report = some target) (stop : report.stop = .fixed) :
    Fixed ops target :=
  (next_none_iff target).mp (Driver.check_fixed hit stop)

theorem check_exhausted {fuel : Nat} {report : Report Action}
    (hit : (driver ops).check fuel source report = some target) (stop : report.stop = .exhausted) :
    report.sites.length = fuel ∧ ¬ Fixed ops target :=
  Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Worklist.Combined.check_exhausted hit stop

theorem visit_sound (s : Output P params results l) (action : Action)
    (zeroLaw : m.run ops.zero .nil = some ⟨0⟩) (scaleLaw : EvalScale.Law m ops.factor ops.scale) :
    Dedup.Preserves m env s (visit ops s action) :=
  Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Worklist.Combined.visit_sound s action zeroLaw scaleLaw

/-- An accepted receipt preserves native ordered partial observations
and class validity for fixed and exhausted reports alike. -/
theorem check_sound {fuel : Nat} {report : Report Action}
    (hit : (driver ops).check fuel source report = some target)
    (zeroLaw : m.run ops.zero .nil = some ⟨0⟩) (scaleLaw : EvalScale.Law m ops.factor ops.scale) :
    Dedup.Preserves m env source target :=
  Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Worklist.Combined.check_sound hit zeroLaw scaleLaw

end Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Worklist.Combined
