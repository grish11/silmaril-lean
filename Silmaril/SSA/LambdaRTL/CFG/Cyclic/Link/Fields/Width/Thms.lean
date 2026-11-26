module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Width.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Institution.Thms
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Width.Traversal
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Width.Refinement

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Width

open Comparison

variable {V F α : Type} [DecidableEq V] {a b : Nat}
variable {left right : Graph V F a b} {inputs : Fin a → Nat} {outputs : Fin b → Nat}

/-- The dependent route predicts the actual result of the named CFG on a
packed input. A checked cycle stays private at the widths of its labels. -/
theorem entryOutcome_sound (model : PairModel F Part α) (profile : Profile left inputs outputs)
    (input : Fin a) (packet : Fin (inputs input) → α) (result : Part (Fin b × α))
    (found : (entryOutcome profile input).predict model.val packet = some result) :
    left.denote model.val (input, encode model.val packet) = result :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Width.entry_sound model profile input packet result found

/-- The same observation through the compiled named SSA class, from any
store holding the packed input in the designated register. -/
theorem namedSSA_entryOutcome_sound [Inhabited V] (model : PairModel F Part α)
    (profile : Profile left inputs outputs) (input : Fin a) (packet : Fin (inputs input) → α)
    (store : V → α) (packedInput : store default = encode model.val packet) (result : Part (Fin b × α))
    (found : (entryOutcome profile input).predict model.val packet = some result) :
    ssaClassObserve model (namedSSAClass input (Quotient.mk _ left)) store = publicResult <$> result := by
  rw [namedSSAClass_observe, packedInput]
  exact congrArg (fun value => publicResult <$> value) (entryOutcome_sound model profile input packet result found)

/-- Compiled named SSA refinement restricted to stores with packed inputs. -/
theorem namedSSA_sat_iff [Inhabited V] (model : PairModel F Part α) (left right : Graph V F a b) :
    Sat inputs model left right ↔ ∀ (input : Fin a) (packet : Fin (inputs input) → α) (store : V → α),
      store default = encode model.val packet →
      ssaClassObserve model (namedSSAClass input (Quotient.mk _ left)) store ≤
        ssaClassObserve model (namedSSAClass input (Quotient.mk _ right)) store := by
  simp only [namedSSAClass_observe, publicResult_le_iff]
  refine ⟨?_, fun sat i packet => sat i packet (fun _ => encode model.val packet) rfl⟩
  intro sat i packet store packed
  rw [packed]
  exact sat i packet

theorem separates_of_distinct (model : PairModel F Part α) (distinct : ∃ x y : α, x ≠ y) :
    Separates inputs outputs model :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Width.separates model distinct

theorem refinement?_eq_none_iff (first : Profile left inputs outputs) (second : Profile right inputs outputs) :
    refinement? first second = none ↔ ¬ (EntryTyped first ∧ EntryTyped second) :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Width.refinement_none first second

theorem refinement_sound (model : PairModel F Part α) (first : Profile left inputs outputs)
    (second : Profile right inputs outputs) (accepted : refinement? first second = some true) :
    Sat inputs model left right :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Width.refinement_sound first second model accepted

/-- Both graphs share the external width families. In a separating model
the checker decides refinement restricted to packed inputs. -/
theorem refinement?_eq_some_iff (model : PairModel F Part α) (separating : Separates inputs outputs model)
    (first : Profile left inputs outputs) (second : Profile right inputs outputs) (verdict : Bool) :
    refinement? first second = some verdict ↔ (EntryTyped first ∧ EntryTyped second) ∧
      (verdict = true ↔ Sat inputs model left right) :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Width.refinement_some first second model separating verdict

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Width
