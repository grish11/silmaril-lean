module

import Silmaril.Languages.Python.Core.Closure.Thms

open Silmaril.Languages.Python.Core.Closure

private def parentLayout : Layout := ⟨1, 2, 1⟩
private def ancestorCell : CellId := ⟨0⟩
private def parent : Heap × Frame parentLayout :=
  Frame.fresh (Heap.empty.reserve 1) (fun _ => ancestorCell)

private def child : CodeRef := ⟨37, ⟨0, 0, 3⟩⟩
private def firstOwned : Fin parentLayout.owned := ⟨0, by decide⟩
private def secondOwned : Fin parentLayout.owned := ⟨1, by decide⟩
private def parentCapture : Fin parentLayout.captures := ⟨0, by decide⟩

-- Interleave two owned cells with an incoming capture, in child order.
private def capturePlan : Fin child.layout.captures → CaptureSlot parentLayout :=
  fun index =>
    if index.val = 0 then .owned secondOwned
    else if index.val = 1 then .forwarded parentCapture else .owned firstOwned

private def closure : Function := parent.2.closure child capturePlan
private def firstCapture : Fin closure.code.layout.captures := ⟨0, by decide⟩
private def secondCapture : Fin closure.code.layout.captures := ⟨1, by decide⟩

example : closure.captures.toList = [⟨2⟩, ⟨0⟩, ⟨1⟩] := rfl

example : parent.2.read parent.1 (.owned secondOwned) = .error (.defined (.unboundOwned 1)) := rfl

private def afterCapture : Heap × Frame closure.code.layout := closure.freshFrame parent.1

example : afterCapture.2.read afterCapture.1 (.capture firstCapture) =
    .error (.defined (.unboundCapture 0)) := rfl

-- The child reads the same cell after a later parent write.
example : (do
    let (heap, _) ← parent.2.write afterCapture.1 (.owned secondOwned) (.int 42)
    afterCapture.2.read heap (.capture firstCapture)) = .ok (.int 42) := rfl

-- Updating the forwarded ancestor cell reaches the original identity.
example : (do
    let (heap, _) ← afterCapture.2.write afterCapture.1 (.capture secondCapture) (.int (-3))
    parent.2.read heap (.capture parentCapture)) = .ok (.int (-3)) := rfl

example : Heap.empty.read ancestorCell (.unboundCapture 0) =
    .error (.danglingCell ancestorCell) := rfl

#print axioms Heap.lookup_reserve_old
#print axioms Heap.write_spec
#print axioms Frame.fresh_owned_injective
#print axioms Frame.capture_at
#print axioms Function.ofCaptureList_order
#print axioms Frame.read_capture_after_owned_write
