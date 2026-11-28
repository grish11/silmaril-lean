module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Defs
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Block
import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Thms

@[expose] public section

namespace Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean

open Silmaril.SSA.LambdaRTL Silmaril.SSA.LambdaRTL.CFG
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields (StoreAgrees read? read?_eval packed packed_eval)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Width (Profile)

variable {V K F α : Type} [DecidableEq V] [DecidableEq F] {a b n : Nat}

@[simp] private theorem slotBit_bitSlot (flag : Bool) : slotBit (bitSlot flag) = flag := by
  cases flag <;> rfl

private theorem body_sound (table : PrimitiveTable F) (model : BooleanModel F α)
    (compatible : table.Compatible model) (width : K → Nat) (body : Body V K F)
    {env : V → Option (Val (Fin 2))} {store : V → α}
    (agrees : StoreAgrees model.pairModel.val (model.bit ∘ slotBit) env store)
    {result : Part (K × α)}
    (found : (primitiveBody table width env body).predict (At.render model) = some result) :
    body.evalJump model.pairModel.val store = result := by
  induction body generalizing env store with
  | let1 dst op tail ih =>
    cases op with
    | val value =>
      cases read : read? env value with
      | none => simp [primitiveBody, read, Step.predict] at found
      | some shape =>
        simp only [Body.evalJump, Body.exec, Op.eval, pure_bind, read?_eval agrees read]
        exact ih (agrees.update dst shape) (by simpa [primitiveBody, read] using found)
    | app symbol value =>
      cases lookup : table.lookup symbol with
      | none => cases read : read? env value <;> simp [primitiveBody, lookup, read, Step.predict] at found
      | some row =>
        cases read : read? env value with
        | none => simp [primitiveBody, lookup, read, Step.predict] at found
        | some shape =>
          cases shape with
          | unit | pair _ _ => simp [primitiveBody, lookup, read, Step.predict] at found
          | var slot =>
            have evaluated : value.eval model.pairModel.val store = model.bit (slotBit slot) :=
              read?_eval agrees read
            have app := compatible symbol row lookup (slotBit slot)
            cases reply : row.reply (slotBit slot) with
            | none =>
              have equal : Part.none = result := by simpa [primitiveBody, lookup, read, reply, Step.predict] using found
              simp only [Body.evalJump, Body.exec, Op.eval, evaluated, app, reply]
              exact (Part.bind_none _).trans equal
            | some flag =>
              simp only [Body.evalJump, Body.exec, Op.eval, evaluated, app, reply, ← Part.pure_eq_some, pure_bind]
              have updated := agrees.update dst (.var (bitSlot flag))
              simp only [Val.eval, Function.comp_apply, slotBit_bitSlot] at updated
              exact ih updated (by simpa [primitiveBody, lookup, read, reply] using found)
    | _ => simp [primitiveBody, Step.predict] at found
  | let2 left right op tail ih =>
    cases op with
    | val value =>
      cases read : read? env value with
      | none => simp [primitiveBody, read, Step.predict] at found
      | some shape =>
        cases shape with
        | var _ | unit => simp [primitiveBody, read, Step.predict] at found
        | pair fst snd =>
          simp only [Body.evalJump, Body.exec, Op.eval, pure_bind, read?_eval agrees read, Val.eval,
            model.pairModel.property.unpair_pair]
          exact ih ((agrees.update left fst).update right snd) (by simpa [primitiveBody, read] using found)
    | _ => simp [primitiveBody, Step.predict] at found
  | term term =>
    cases checked : select? width slotBit env term with
    | none => simp [primitiveBody, checked, Step.predict] at found
    | some edge =>
      have equal : Part.some (At.render (width := width) model ⟨edge.1, slotBit ∘ edge.2⟩) = result := by
        simpa [primitiveBody, checked, Step.predict] using found
      exact (select_sound model width slotBit env store term edge agrees checked).trans equal

theorem primitive_block_sound (table : PrimitiveTable F) (model : BooleanModel F α)
    (compatible : table.Compatible model) (width : K → Nat) (block : Block V K F)
    (packet : Packet n) (store : V → α) {result : Part (K × α)}
    (found : (primitiveBlock table width block packet).predict (At.render model) = some result) :
    block.body.evalJump model.pairModel.val (upd store block.param (encodePacket model packet)) = result := by
  apply body_sound table model compatible width block.body _ found
  intro reg shape read
  by_cases same : reg = block.param
  · subst reg
    have equal : packed (fun i => .var (bitSlot (packet i))) = shape := by simpa [upd] using read
    subst shape
    simp [upd, packed_eval, Val.eval, encodePacket, Function.comp_def]
  · simp [upd, same] at read

theorem primitive_advance_sound {graph : Graph V F a b} {inputs : Fin a → Nat} {outputs : Fin b → Nat}
    (table : PrimitiveTable F) (model : BooleanModel F α) (compatible : table.Compatible model)
    (profile : Profile graph inputs outputs) : StepSound model profile (primitiveAdvance table profile) := by
  intro state result found
  unfold primitiveAdvance at found
  cases checked : primitiveBlock table profile.width (graph.block state.1) state.2 with
  | unsupported => simp [checked, Step.predict] at found
  | undefined =>
    have block := primitive_block_sound table model compatible profile.width (graph.block state.1) state.2
      (fun _ => model.pairModel.val.unit) (result := Part.none) (by rw [checked]; rfl)
    simp only [Graph.step, block]
    exact (Part.map_none _).trans (Option.some.inj (by simpa [checked, Step.predict] using found))
  | next next =>
    have block := primitive_block_sound table model compatible profile.width (graph.block state.1) state.2
      (fun _ => model.pairModel.val.unit) (result := Part.some (next.render model)) (by rw [checked]; rfl)
    have equal : Part.some (.inr (next.render model)) = result := by simpa [checked, Step.predict] using found
    exact (by simp [Graph.step, block] :
      graph.step model.pairModel.val (.inl state.1, encodePacket model state.2) =
        Part.some (.inr (next.render model))).trans equal

end Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean
