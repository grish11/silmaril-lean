module

public import Silmaril.Wasm.Component.Reference.Canon.Handles.Defs
import Silmaril.Wasm.Component.Reference.Canon.Prog.Thms

namespace Silmaril.Proofs.Wasm.Component.Reference.Canon.Handles.AsyncLift

open Silmaril.Wasm.Component Silmaril.Wasm.Component.AsyncRef Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime

variable {E : CoreEngine} {σ : Type}

private theorem trapThen {α β : Type} (reason : TrapReason) (next : α → P E σ β) :
    Prog.bind (Canon.trap reason) next = Canon.trap reason := by
  change Prog.op (S := Eff E σ) (.trap reason) _ = Prog.op (S := Eff E σ) (.trap reason) _
  congr 1
  funext response
  exact nomatch response

public theorem source (lim : Limits) (kind : EndKind) (cx : LiftLowerContext E)
    (t : Option (WIT.ClosedType RtId)) (slot : Nat) :
    (liftAsyncValue lim kind cx t slot : P E σ EndId) = (do
      let source ← getStore
      match source.inst? cx.inst with
      | none => internal "dangling arena id"
      | some inst =>
        match inst.removeHandle? slot with
        | none => trap (.unknownHandle slot)
        | some (entry, _) =>
          modifyInst cx.inst (InstState.removeHandle slot)
          match entry with
          | .waitable (.end_ identity) =>
            let reached ← getStore
            match checkLiftEndRead kind t (reached.end? identity) with
            | .error reason => trap reason
            | .ok () =>
              modifyStore (HandleSt.releaseEnd identity)
              return identity
          | _ => trap .wrongHandleType) := by
  unfold liftAsyncValue handlesRemove getInst getObj CStore.inst?
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc]
  congr 1
  funext source
  cases ArenaField.insts.get? source cx.inst with
  | none => simp only [internal, trapThen]
  | some inst =>
    simp only [Prog.pure_bind']
    cases inst.removeHandle? slot with
    | none => simp only [trapThen]
    | some pair =>
      obtain ⟨entry, remaining⟩ := pair
      simp only [Prog.bind_assoc, Prog.pure_bind']
      congr 1
      funext issued
      cases entry with
      | resource | errCtx | wset => simp only [checkLiftEnd, trapThen]
      | waitable waitable =>
        cases waitable with
        | subtask => simp only [checkLiftEnd, trapThen]
        | end_ identity =>
          unfold checkLiftEnd getObj CStore.end?
          simp only [Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc]
          congr 1
          funext reached
          cases ArenaField.ends.get? reached identity with
          | none => simp only [checkLiftEndRead, internal, trapThen]
          | some en =>
            simp only [Prog.pure_bind', checkLiftEndRead, trapIf, Prog.pure_eq]
            split
            · rw [trapThen]
            · rw [Prog.pure_bind']
              split
              · rw [trapThen]
              · rw [Prog.pure_bind']
                split
                · rw [trapThen]
                · rw [Prog.pure_bind']
                  split
                  · rw [trapThen]
                  · rfl

end Silmaril.Proofs.Wasm.Component.Reference.Canon.Handles.AsyncLift
