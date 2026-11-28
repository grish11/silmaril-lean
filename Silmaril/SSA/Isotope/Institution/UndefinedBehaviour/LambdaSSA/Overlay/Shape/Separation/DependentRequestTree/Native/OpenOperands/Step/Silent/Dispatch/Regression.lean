module

import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Silent.Dispatch.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.ExitUB.Thms

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch.Regression

open Category.FiniteIteration hiding Table Row
open CFG.Dependent (Packet)
open CFG.Dependent.Native (withExitUB)
open Syntax (Expr Payload StatePrimitives model)
open LambdaSSA.Region (packedExitType)
open TwoRequest (Exits)

private abbrev Bit : Syntax.Ty := .coprod .unit .unit
private abbrev Labels : List Syntax.Ty := [Bit, Bit]

private inductive Op where
  | read
  deriving DecidableEq

private instance : HasTy Op Syntax.Ty := ⟨fun _ => Bit, fun _ => packedExitType [Bit]⟩
private abbrev sig : RequestSignature Op := ⟨fun _ => [Bit], fun _ => rfl⟩

private def leftBit : Payload Bit := ⟨.inl .unit, .inl .unit⟩
private def rightBit : Payload Bit := ⟨.inr .unit, .inr .unit⟩

private theorem bits (a : Payload Bit) : a ∈ [leftBit, rightBit] := by
  obtain ⟨_, typed⟩ := a
  cases typed with
  | inl typed => cases typed; exact List.Mem.head _
  | inr typed => cases typed; exact List.Mem.tail _ (List.Mem.head _)

private def bitsAt (i : Fin Labels.length) : List (Payload (Labels.get i)) :=
  Fin.cases (motive := fun j => List (Payload (Labels.get j))) [leftBit, rightBit]
    (fun j => by obtain rfl := Fin.eq_zero j; exact [leftBit, rightBit]) i

private theorem completeBitsAt (i : Fin Labels.length) (a : Payload (Labels.get i)) : a ∈ bitsAt i := by
  refine Fin.cases (motive := fun i => ∀ a : Payload (Labels.get i), a ∈ bitsAt i) ?_ ?_ i a
  · exact bits
  · intro j
    obtain rfl := Fin.eq_zero j
    exact bits

private def inventory : ConfigurationEnumeration Labels where
  configs := (List.finRange Labels.length).flatMap fun i => (bitsAt i).map fun a => ⟨i, a⟩
  complete := fun ⟨i, a⟩ => List.mem_flatMap.mpr
    ⟨i, List.mem_finRange i, List.mem_map.mpr ⟨a, completeBitsAt i a, rfl⟩⟩

private def route (onLeft : Expr [.unit, Bit, Bit] Bit) (body : OpenOperands.Row sig Labels [Bit, Bit])
    (selectExit : Bool) : Table sig Labels where
  entry := 0
  row := Fin.cases (motive := fun i => Row sig Labels [Labels.get i, Bit])
    (.dispatch (.var 0) 0 1 onLeft (.inr (.var 0)))
    (fun i => by obtain rfl := Fin.eq_zero i; exact .guarded body)
  selected tag := (tag == 1) && selectExit

private def detour (selected : Bool) := route (.inr (.var 0)) (.exit 1) selected
private def cycle := route (.inl (.var 0)) (.exit 1) true

private abbrev start : Packet Labels := ⟨0, leftBit⟩
private abbrev changed : Packet Labels := ⟨0, rightBit⟩

-- The first hop revisits label zero with another packet. The next hop
-- takes the other arm, and the terminal keeps ordered exit one.
example : (detour false).step leftBit start = .inl changed := rfl
example : (detour false).step leftBit changed = .inl ⟨1, rightBit⟩ := rfl
example : (detour false).scan leftBit 2 start = none := rfl
example : (detour false).head? (detour false).native inventory leftBit start = some (.exit 1 false) := rfl

example (prim : StatePrimitives Op Nat) (s : Nat) :
    Shape.denote (withExitUB (detour false).native (detour false).selected)
      (model prim ((detour false).visible.bindings leftBit)) s =
      WithTop.some {Outcome.ret (1 : Fin 2) .unit s} := by
  exact ((detour false).observe_entry _ rfl inventory leftBit prim s).trans
    ((detour false).observe_step inventory leftBit prim start s)

example (prim : StatePrimitives Op Nat) (s : Nat) :
    Shape.denote (withExitUB (detour true).native (detour true).selected)
      (model prim ((detour true).visible.bindings leftBit)) s = ⊤ := by
  exact ((detour true).observe_entry _ rfl inventory leftBit prim s).trans
    ((detour true).observe_step inventory leftBit prim start s)

-- The alternative left arm repeats the full typed configuration. Its
-- selected exit remains unreachable from this caller.
example : cycle.step leftBit start = .inl start := rfl
example : cycle.scan leftBit inventory.configs.length start = none := rfl
example : (cycle.head inventory leftBit start).query? (0 : Fin 1) = none := rfl
example : cycle.head? cycle.native inventory leftBit changed = some (.exit 1 true) := rfl

example (prim : StatePrimitives Op Nat) (s : Nat) :
    Shape.denote (withExitUB cycle.native cycle.selected)
      (model prim (cycle.visible.bindings leftBit)) s = WithTop.some {Outcome.diverge} := by
  exact (cycle.observe_entry _ rfl inventory leftBit prim s).trans
    (cycle.observe_step inventory leftBit prim start s)

example : cycle.head? (detour true).native inventory leftBit start = none := rfl

-- One guarded row fixes the head kind at a label, even when its argument
-- value can vary. These two normalized heads cannot share that label.
example (g : GuardedTable sig Labels) (caller : Payload (Labels.get g.entry)) :
    ¬ ∀ p, g.head caller p = cycle.head inventory leftBit p := by
  intro agrees
  have left := agrees start
  have right := agrees changed
  change g.head caller start = .diverge at left
  change g.head caller changed = .exit 1 true at right
  cases row : g.row 0 <;> simp [OpenOperands.Table.head, row] at left right

private def request :=
  route (.inr (.var 0)) (.request .read (.var 0) (fun _ => 0) (fun i => by
    obtain rfl := Fin.eq_zero i
    rfl)) false

private def respond : StatePrimitives Op Nat := fun _ a s =>
  if a.val = rightBit.val then .fault (s + 1) else .diverge

example (s : Nat) :
    Shape.denote (withExitUB request.native request.selected)
      (model respond (request.visible.bindings leftBit)) s = WithTop.some {Outcome.fault (s + 1)} := by
  exact (request.observe_entry _ rfl inventory leftBit respond s).trans
    (request.observe_step inventory leftBit respond start s)

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch.Regression
