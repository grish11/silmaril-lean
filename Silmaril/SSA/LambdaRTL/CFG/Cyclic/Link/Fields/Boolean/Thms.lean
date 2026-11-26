module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Institution.Thms
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Block
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Traversal
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Refinement
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Primitive

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
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.refinement_at_with model first second
    (pureAdvance first) (pureAdvance second) (Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.pure_sound model first)
    (Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.pure_sound model second) input packet supportedL supportedR

theorem refinementAt?_eq_none_iff (first : Profile left inputs outputs) (second : Profile right inputs outputs)
    (input : Fin a) (packet : Packet (inputs input)) :
    refinementAt? first second input packet = none ↔
      ¬ ((entryOutcome first input packet).supported ∧ (entryOutcome second input packet).supported) :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.refinement_at_none_with first second
    (pureAdvance first) (pureAdvance second) input packet

theorem refinement?_eq_none_iff (first : Profile left inputs outputs) (second : Profile right inputs outputs) :
    refinement? first second = none ↔ ¬ (Supported first ∧ Supported second) :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.refinement_none_with first second
    (pureAdvance first) (pureAdvance second)

theorem refinement?_eq_some_iff (model : BooleanModel F α) (first : Profile left inputs outputs)
    (second : Profile right inputs outputs) (verdict : Bool) :
    refinement? first second = some verdict ↔ (Supported first ∧ Supported second) ∧
      (verdict = true ↔ Sat inputs model left right) :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.refinement_some_with model first second
    (pureAdvance first) (pureAdvance second) (Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.pure_sound model first)
    (Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.pure_sound model second) verdict

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

section

variable [DecidableEq F]

/-- The local check predicts either a typed jump or a certified undefined
computation. Its result is independent of the store outside the packet. -/
theorem primitiveBlock_evalJump (table : PrimitiveTable F) (model : BooleanModel F α)
    (compatible : table.Compatible model) (width : K → Nat) (block : Block V K F)
    (packet : Packet n) (store : V → α) {result : Part (K × α)}
    (found : (primitiveBlock table width block packet).predict (At.render model) = some result) :
    block.body.evalJump model.pairModel.val (upd store block.param (encodePacket model packet)) = result :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.primitive_block_sound
    table model compatible width block packet store found

theorem primitiveEntryOutcome_sound (table : PrimitiveTable F) (model : BooleanModel F α)
    (compatible : table.Compatible model) (profile : Profile left inputs outputs)
    (input : Fin a) (packet : Packet (inputs input)) (result : Part (Fin b × α))
    (found : (primitiveEntryOutcome table profile input packet).predict model = some result) :
    left.denote model.pairModel.val (input, encodePacket model packet) = result :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.entry_with_sound model profile
    (primitiveAdvance table profile)
    (Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.primitive_advance_sound table model compatible profile)
    input packet result found

theorem namedSSA_primitiveEntryOutcome_sound [Inhabited V] (table : PrimitiveTable F)
    (model : BooleanModel F α) (compatible : table.Compatible model) (profile : Profile left inputs outputs)
    (input : Fin a) (packet : Packet (inputs input)) (store : V → α)
    (packed : store default = encodePacket model packet) (result : Part (Fin b × α))
    (found : (primitiveEntryOutcome table profile input packet).predict model = some result) :
    ssaClassObserve model.pairModel (namedSSAClass input (Quotient.mk _ left)) store = publicResult <$> result := by
  rw [namedSSAClass_observe, packed]
  exact congrArg (fun value => publicResult <$> value)
    (primitiveEntryOutcome_sound table model compatible profile input packet result found)

theorem primitiveRefinement?_eq_none_iff (table : PrimitiveTable F) (first : Profile left inputs outputs)
    (second : Profile right inputs outputs) :
    primitiveRefinement? table first second = none ↔
      ¬ (PrimitiveSupported table first ∧ PrimitiveSupported table second) :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.refinement_none_with first second
    (primitiveAdvance table first) (primitiveAdvance table second)

/-- The verdict is exact for the compiled named observations in any
compatible pair-lawful Part model on stores holding Boolean input packets. -/
theorem primitiveRefinement?_eq_some_packed_iff [Inhabited V] (table : PrimitiveTable F)
    (model : BooleanModel F α) (compatible : table.Compatible model) (first : Profile left inputs outputs)
    (second : Profile right inputs outputs) (verdict : Bool) :
    primitiveRefinement? table first second = some verdict ↔
      (PrimitiveSupported table first ∧ PrimitiveSupported table second) ∧
        (verdict = true ↔ ∀ input, packedSat (inputs input) model
          (namedSSAClass input (Quotient.mk _ left)) (namedSSAClass input (Quotient.mk _ right))) :=
  (Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.refinement_some_with model first second
    (primitiveAdvance table first) (primitiveAdvance table second)
    (Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.primitive_advance_sound table model compatible first)
    (Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.primitive_advance_sound table model compatible second)
    verdict).trans (and_congr_right fun _ => iff_congr Iff.rfl (namedSSA_sat_iff model left right))

end

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean
