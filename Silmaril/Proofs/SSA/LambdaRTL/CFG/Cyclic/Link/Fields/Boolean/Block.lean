module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Defs
import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Thms

@[expose] public section

namespace Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean

open Silmaril.SSA.LambdaRTL Silmaril.SSA.LambdaRTL.CFG
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields (Route StoreAgrees read? read?_eval termTo_evalJump blockWith? blockWith_evalJump)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Width (Profile)

variable {V K F α : Type} [DecidableEq V] {a b n : Nat}

theorem select_sound (model : BooleanModel F α) (width : K → Nat) (packet : Packet n)
    (env : V → Option (Val (Fin n))) (store : V → α) (term : Term V K F)
    (result : (target : K) × Route n (width target))
    (agrees : StoreAgrees model.pairModel.val (model.bit ∘ packet) env store)
    (accepted : select? width packet env term = some result) :
    (Body.term term).evalJump model.pairModel.val store = pure (result.1, encodePacket model (packet ∘ result.2)) := by
  cases term with
  | br target value => exact termTo_evalJump model.pairModel.val _ width agrees _ accepted
  | case op yes yesArm no noArm =>
    cases op with
    | val value =>
      cases found : read? env value with
      | none => simp [select?, found] at accepted
      | some shape =>
        cases shape with
        | unit => simp [select?, found] at accepted
        | pair lhs rhs => simp [select?, found] at accepted
        | var field =>
          have evaluated : value.eval model.pairModel.val store = model.bit (packet field) :=
            read?_eval agrees found
          cases flag : packet field
          · have arm := termTo_evalJump model.pairModel.val _ width (agrees.update no .unit) noArm
                (by simpa [select?, found, flag] using accepted)
            simpa only [Body.evalJump, Body.exec, Term.exec, Op.eval, pure_bind, evaluated,
              model.split_bit, flag, Bool.false_eq_true, ite_false, Val.eval, encodePacket, Function.comp_assoc] using arm
          · have arm := termTo_evalJump model.pairModel.val _ width (agrees.update yes .unit) yesArm
                (by simpa [select?, found, flag] using accepted)
            simpa only [Body.evalJump, Body.exec, Term.exec, Op.eval, pure_bind, evaluated,
              model.split_bit, flag, ite_true, Val.eval, encodePacket, Function.comp_assoc] using arm
    | _ => exact nomatch accepted

theorem block_sound (model : BooleanModel F α) (width : K → Nat) (packet : Packet n)
    (block : Block V K F) (store : V → α) {result : (target : K) × Route n (width target)}
    (accepted : blockWith? n (select? width packet) block = some result) :
    block.body.evalJump model.pairModel.val (upd store block.param (encodePacket model packet)) =
      pure (result.1, encodePacket model (packet ∘ result.2)) :=
  blockWith_evalJump model.pairModel (model.bit ∘ packet) (select? width packet) _
    (select_sound model width packet) block store accepted

variable {graph : Graph V F a b} {inputs : Fin a → Nat} {outputs : Fin b → Nat}

theorem private_step (model : BooleanModel F α) (profile : Profile graph inputs outputs)
    (state : At profile.localWidth) {next : At profile.width}
    (edge : next? profile state = some next) :
    graph.step model.pairModel.val (.inl state.1, encodePacket model state.2) =
      Part.some (.inr (next.render model)) := by
  unfold next? at edge
  cases checked : blockWith? (profile.localWidth state.1) (select? profile.width state.2)
    (graph.block state.1) with
  | none => simp [checked] at edge
  | some result =>
    have same : (⟨result.1, state.2 ∘ result.2⟩ : At profile.width) = next := by simpa [checked] using edge
    subst next
    simp [Graph.step, At.render, block_sound model profile.width state.2 (graph.block state.1)
      (fun _ => model.pairModel.val.unit) checked]

theorem pure_sound (model : BooleanModel F α) (profile : Profile graph inputs outputs) :
    StepSound model profile (pureAdvance profile) := by
  intro state result found
  cases checked : next? profile state with
  | none => simp [pureAdvance, checked, Step.predict] at found
  | some next =>
    have same : Part.some (.inr (At.render model next)) = result := by
      simpa [pureAdvance, checked, Step.predict] using found
    exact (private_step model profile state checked).trans same

end Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean
