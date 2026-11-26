module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader.Theta.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.Petri.Defs
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Partial.Thms

/-! Finite coloured completion of the actual original and normalized
numbered θ graphs. Each graph defines its own places and markings. -/

public section

namespace Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader.Theta

open Activation (Inputs)
open Builder.Preheader (Native)
open Diamond (Ty Val ValueSort)
open Loop (thetaRuntime)
open Pure.SubZero (model)
open RVSDG (Tuple)
open RVSDG.NestedTheta (MonadicModel)
open RVSDG.NestedTheta.Partial (observe observe_ofRuntime_eq_some_iff_returns)
open RVSDG.NestedTheta.Petri (Finishes finishes_iff)

variable {inputs carried : List (ValueSort Unit)} {entrySigs headerSigs : List (List (Ty Unit))}
variable {out : ValueSort Unit}

/-- The coloured firing semantics and the partial observation agree on
absence of a finite completed trace for either emitted graph. -/
theorem petri_no_completion_iff_observe_none (program : Program inputs carried entrySigs out)
    (input : Inputs model inputs) :
    (∀ packet, ¬ Finishes (thetaRuntime model) program input packet) ↔
      observe (MonadicModel.ofRuntime (thetaRuntime model)) program input = Part.none := by
  rw [Part.eq_none_iff]
  exact forall_congr' fun packet => not_congr
    ((finishes_iff _ _ _ packet).trans ((observe_ofRuntime_eq_some_iff_returns _ _ _ packet).symm.trans Part.eq_some_iff))

variable (loop : Native inputs carried entrySigs headerSigs out) (input : Inputs model inputs)

/-- Both original and normalized coloured runs complete with the same
finite result packets. Each uses its own firing trace and marking. -/
theorem emit_petri_finishes_iff (packet : Tuple (Val model.value) [.value out]) :
    Finishes (thetaRuntime model) (emit loop) input packet ↔
      Finishes (thetaRuntime model) loop.lowerTheta input packet := by
  cases packet with
  | cons value tail =>
    cases tail
    exact (finishes_iff _ _ _ _).trans ((emit_returns_iff loop input value).trans (finishes_iff _ _ _ _).symm)

/-- Neither side has a finite completed trace exactly when the other
side has none, from the same original input tuple. -/
theorem emit_petri_no_completion_iff :
    (∀ packet, ¬ Finishes (thetaRuntime model) (emit loop) input packet) ↔
      ∀ packet, ¬ Finishes (thetaRuntime model) loop.lowerTheta input packet := by
  simp only [emit_petri_finishes_iff loop input]

end Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader.Theta
