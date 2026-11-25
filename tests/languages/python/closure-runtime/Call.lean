module

import Silmaril.Languages.Python.Core.Closure.Call.Thms

open Silmaril.Languages.Python.Core.Closure Silmaril.Languages.Python.Core.Closure.Call

private def callerLayout : Layout := ⟨1, 1, 0⟩
private def initial : Heap × Frame callerLayout := Frame.fresh Heap.empty Fin.elim0

private def saved : Saved (fun _ => Nat) :=
  ⟨callerLayout, { initial.2 with locals := fun _ => some (.int 5) }, 21⟩

private def cell : CellId := saved.frame.owned ⟨0, by decide⟩
private def calleeCode : CodeRef := ⟨10, ⟨1, 1, 1⟩⟩
private def calleeFunction : Function := Function.ofCaptureList calleeCode [cell] rfl

private def ownedSlot : Fin calleeFunction.code.layout.owned := ⟨0, by decide⟩
private def localSlot : Fin calleeFunction.code.layout.locals := ⟨0, by decide⟩
private def captureSlot : Fin calleeFunction.code.layout.captures := ⟨0, by decide⟩

private def parameters : Parameters calleeFunction.code.layout :=
  ⟨[.owned ownedSlot, .local localSlot], by decide⟩

private def olderLayout : Layout := ⟨0, 0, 0⟩
private def older : Saved (fun _ => Nat) :=
  ⟨olderLayout, (Frame.fresh Heap.empty Fin.elim0).2, 13⟩

private def entered := enter calleeFunction parameters [.int 11, .int 7] initial.1 saved [older]

example : (do
    let entry ← entered
    let owned ← entry.environment.2.read entry.environment.1 (.owned ownedSlot)
    let localValue ← entry.environment.2.read entry.environment.1 (.local localSlot)
    pure (owned, localValue)) = .ok (.int 11, .int 7) := rfl

example : enter calleeFunction parameters [.int 11] initial.1 saved [] =
    .error (.defined (.positionalArity 2 1)) := rfl

-- Address 1 would be allocated as the callee's owned cell. A bad incoming
-- reference to that address is rejected before the allocation.
private def danglingFunction : Function := Function.ofCaptureList calleeCode [⟨1⟩] rfl

example : enter danglingFunction parameters [.int 11, .int 7] initial.1 saved [] =
    .error (.danglingCell ⟨1⟩) := rfl

private def deliver (result : Result) : Except Failure (Exit fun _ => Nat) := do
  let entry ← entered
  let (residual, _) ← entry.environment.2.write entry.environment.1 (.capture captureSlot) (.int 42)
  pure (finish residual entry.stack result)

private def restored (result : Result) : Prop :=
  match deliver result with
  | .ok exit =>
    match exit.delivery with
    | .resume caller observed =>
      caller = saved ∧ exit.stack = [older] ∧ observed = result ∧
        exit.heap.read cell (.unboundOwned 0) = .ok (.int 42)
    | .terminal _ => False
  | .error _ => False

example : restored (.ok (.int 9)) := ⟨rfl, rfl, rfl, rfl⟩
example : restored (.error (.unboundCapture 0)) := ⟨rfl, rfl, rfl, rfl⟩

example :
    (finish (Continuation := fun _ => Nat) Heap.empty [] (.error (.unboundLocal 0))).delivery =
      .terminal (.error (.unboundLocal 0)) := rfl

#print axioms bind_iff
#print axioms bind_preserves_ids
#print axioms enter_capture
#print axioms enter_captures_live
#print axioms enter_complete
#print axioms enter_read
#print axioms enter_preserves_cell
#print axioms finish_after_enter
