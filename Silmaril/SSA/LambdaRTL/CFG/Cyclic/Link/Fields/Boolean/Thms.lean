module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Institution.Thms
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Block
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Traversal
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Refinement

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean

open Comparison
open Width (Profile)

variable {V K F α : Type} [DecidableEq V] {a b n : Nat}
  {left right : Graph V F a b} {inputs : Fin a → Nat} {outputs : Fin b → Nat}

theorem block_evalJump (model : BooleanModel F α) (width : K → Nat) (packet : Packet n)
    (block : Block V K F) (store : V → α) {result : (target : K) × Route n (width target)}
    (accepted : blockWith? n (select? width packet) block = some result) :
    block.body.evalJump model.pairModel.val (upd store block.param (encodePacket model packet)) =
      pure (result.1, encodePacket model (packet ∘ result.2)) :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.block_sound model width packet block store accepted

/-- A supported Boolean packet predicts the actual CFG observation. A
cycle is justified by a repeat of the entire private state. -/
theorem entryOutcome_sound (model : BooleanModel F α) (profile : Profile left inputs outputs)
    (input : Fin a) (packet : Packet (inputs input)) (result : Part (Fin b × α))
    (found : (entryOutcome profile input packet).predict model = some result) :
    left.denote model.pairModel.val (input, encodePacket model packet) = result :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.entry_sound model profile input packet result found

theorem namedSSA_entryOutcome_sound [Inhabited V] (model : BooleanModel F α)
    (profile : Profile left inputs outputs) (input : Fin a) (packet : Packet (inputs input))
    (store : V → α) (packed : store default = encodePacket model packet) (result : Part (Fin b × α))
    (found : (entryOutcome profile input packet).predict model = some result) :
    ssaClassObserve model.pairModel (namedSSAClass input (Quotient.mk _ left)) store = publicResult <$> result := by
  rw [namedSSAClass_observe, packed]
  exact congrArg (fun value => publicResult <$> value) (entryOutcome_sound model profile input packet result found)

theorem refinementAt?_iff (model : BooleanModel F α) (first : Profile left inputs outputs)
    (second : Profile right inputs outputs) (input : Fin a) (packet : Packet (inputs input))
    (supportedL : (entryOutcome first input packet).supported)
    (supportedR : (entryOutcome second input packet).supported) :
    refinementAt? first second input packet = some true ↔
      left.denote model.pairModel.val (input, encodePacket model packet) ≤
        right.denote model.pairModel.val (input, encodePacket model packet) :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.refinement_at model first second input packet supportedL supportedR

theorem refinementAt?_eq_none_iff (first : Profile left inputs outputs) (second : Profile right inputs outputs)
    (input : Fin a) (packet : Packet (inputs input)) :
    refinementAt? first second input packet = none ↔
      ¬ ((entryOutcome first input packet).supported ∧ (entryOutcome second input packet).supported) :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.refinement_at_none first second input packet

theorem refinement?_eq_none_iff (first : Profile left inputs outputs) (second : Profile right inputs outputs) :
    refinement? first second = none ↔ ¬ (Supported first ∧ Supported second) :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.refinement_none first second

theorem refinement?_eq_some_iff (model : BooleanModel F α) (first : Profile left inputs outputs)
    (second : Profile right inputs outputs) (verdict : Bool) :
    refinement? first second = some verdict ↔ (Supported first ∧ Supported second) ∧
      (verdict = true ↔ Sat inputs model left right) :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.refinement_some model first second verdict

theorem namedSSA_sat_iff [Inhabited V] (model : BooleanModel F α) (left right : Graph V F a b) :
    Sat inputs model left right ↔ ∀ input, packedSat (inputs input) model
      (namedSSAClass input (Quotient.mk _ left)) (namedSSAClass input (Quotient.mk _ right)) := by
  simp only [packedSat, namedSSAClass_observe, publicResult_le_iff]
  refine ⟨?_, fun sat i packet => sat i packet (fun _ => encodePacket model packet) rfl⟩
  intro sat i packet store packed
  rw [packed]
  exact sat i packet

/-- The verdict decides the compiled named comparison on Boolean-packed
stores. Other values and unsupported primitives are outside this comparison. -/
theorem refinement?_eq_some_packed_iff [Inhabited V] (model : BooleanModel F α)
    (first : Profile left inputs outputs) (second : Profile right inputs outputs) (verdict : Bool) :
    refinement? first second = some verdict ↔ (Supported first ∧ Supported second) ∧
      (verdict = true ↔ ∀ input, packedSat (inputs input) model
        (namedSSAClass input (Quotient.mk _ left)) (namedSSAClass input (Quotient.mk _ right))) :=
  (refinement?_eq_some_iff model first second verdict).trans (and_congr_right fun _ =>
    iff_congr Iff.rfl (namedSSA_sat_iff model left right))

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean
