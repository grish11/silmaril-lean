module

import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Silent.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.TwoRequest.Thms

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent

open Category.FiniteIteration hiding Row Table
open CFG.Dependent (Packet pack)
open CFG.Dependent.Native (withExitUB)
open LambdaSSA.Region (packedExitType)
open Syntax (Expr Payload StatePrimitives Primitives model)

universe v

private inductive Op where
  | request
  deriving DecidableEq

private abbrev Bit : Syntax.Ty := .coprod .unit .unit
private abbrev UnitTy : Syntax.Ty := .unit
private abbrev Packets : List Syntax.Ty := [Bit, Bit]
private abbrev replies (_ : Op) : List Syntax.Ty := [Bit]
private instance : HasTy Op Syntax.Ty := ⟨fun _ => Bit, fun f => packedExitType (replies f)⟩
private abbrev sig : RequestSignature Op := ⟨replies, fun _ => rfl⟩

private def leftBit : Payload Bit := ⟨.inl .unit, .inl .unit⟩
private def rightBit : Payload Bit := ⟨.inr .unit, .inr .unit⟩
private def unitPacket : Payload UnitTy := ⟨.unit, .unit⟩

private def callers : CallerEnumeration UnitTy := ⟨[unitPacket], fun a => by
  obtain ⟨_, typed⟩ := a
  cases typed
  exact List.Mem.head _⟩

private theorem bits (a : Payload Bit) : a ∈ [leftBit, rightBit] := by
  obtain ⟨_, typed⟩ := a
  cases typed with
  | inl typed => cases typed; exact List.Mem.head _
  | inr typed => cases typed; exact List.Mem.tail _ (List.Mem.head _)

private def replyPackets : ReplyEnumeration sig where
  packets _ := [⟨0, leftBit⟩, ⟨0, rightBit⟩]
  complete _ packet := by
    obtain ⟨tag, b⟩ := packet
    obtain rfl := Fin.eq_zero tag
    rcases List.mem_cons.mp (bits b) with rfl | h
    · exact List.Mem.head _
    · obtain rfl := List.mem_singleton.mp h
      exact List.Mem.tail _ (List.Mem.head _)

private def bitAt (i : Fin Packets.length) : CallerEnumeration (Packets.get i) :=
  Fin.cases (motive := fun i => CallerEnumeration (Packets.get i)) ⟨_, bits⟩
    (fun i => by obtain rfl := Fin.eq_zero i; exact ⟨_, bits⟩) i

private def inventory : ConfigurationEnumeration Packets where
  configs := (List.finRange Packets.length).flatMap fun i => (bitAt i).packets.map fun p => ⟨i, p⟩
  complete := fun ⟨i, a⟩ => List.mem_flatMap.mpr
    ⟨i, List.mem_finRange i, List.mem_map.mpr ⟨a, (bitAt i).complete a, rfl⟩⟩

private def request (arg : Expr [Bit, Bit] Bit) : OpenOperands.Row sig Packets [Bit, Bit] :=
  .request .request arg (fun _ => 1) (fun i => by obtain rfl := Fin.eq_zero i; rfl)

-- The first reply changes the packet. The native jump reads the caller to
-- replace that packet before the next request, at the same final store.
private def detour : Table sig Packets where
  entry := 0
  row := Fin.cases (motive := fun i => Row sig Packets [Packets.get i, Bit])
    (.guarded (request (.var 0))) (fun i => by
      obtain rfl := Fin.eq_zero i
      exact .jump 0 (.var 1))
  selected _ := false

private def direct : GuardedTable sig Packets where
  entry := 0
  row := Fin.cases (motive := fun i => OpenOperands.Row sig Packets [Packets.get i, Bit])
    (request (.var 0)) (fun i => by
      obtain rfl := Fin.eq_zero i
      exact request (.var 1))
  selected _ := false

private abbrev peer := Table.ofGuarded direct
private def decode (_ : Payload UnitTy) := leftBit

private theorem normalizedNative : direct.native = (detour.normalized rfl).native :=
  (detour.normalized rfl).checked_reemission rfl

private theorem equivalent {σ : Type v} (prim : StatePrimitives Op σ) (a : Payload Bit) (s : σ) :
    Shape.denote (withExitUB detour.native detour.selected) (model prim (detour.visible.bindings a)) s =
      Shape.denote (withExitUB direct.native direct.selected) (model prim (direct.bindings a)) s :=
  by
    rw [detour.normalized_observes rfl detour.native rfl a prim s, ← normalizedNative]
    rfl

example : (detour.normalized rfl).reachableCutoff direct callers decode decode replyPackets inventory inventory = 3 :=
  rfl

example : detour.checkEntries? peer detour.native peer.native callers decode decode
    replyPackets inventory inventory = some true :=
  (Table.checkEntries_accepts_iff.{0,0} rfl rfl).mpr (fun _ _ prim s => (equivalent prim leftBit s).le)

example : detour.checkEntries? peer peer.native peer.native callers decode decode
    replyPackets inventory inventory = none := rfl

example :
    (match detour.head? detour.native leftBit ⟨1, rightBit⟩ with
     | some (.ready (.request _ arg _)) => arg.val == leftBit.val
     | _ => false) = true := rfl

private def prim : Primitives Op 2 := fun _ a s =>
  if s = 0 then .ret (pack (L := [Bit]) ⟨0, rightBit⟩) 1
  else if a.val = leftBit.val then .fault 1 else .diverge

example : Shape.denote (withExitUB detour.native detour.selected)
      (model prim (detour.visible.bindings leftBit)) 0 = WithTop.some {Outcome.fault (1 : Fin 2)} := by
  refine (equivalent prim leftBit 0).trans ((direct.observe_entry direct.native rfl leftBit prim 0).trans ?_)
  exact (direct.observe_step leftBit prim ⟨0, leftBit⟩ 0).trans
    (direct.observe_step leftBit prim ⟨1, rightBit⟩ 1)

private abbrev Loop := [Bit]
private def single : ConfigurationEnumeration Loop :=
  ⟨[⟨0, leftBit⟩, ⟨0, rightBit⟩], fun ⟨i, p⟩ => by
    obtain rfl := Fin.eq_zero i
    rcases List.mem_cons.mp (bits p) with rfl | right
    · exact List.Mem.head _
    · obtain rfl := List.mem_singleton.mp right
      exact List.Mem.tail _ (List.Mem.head _)⟩

-- Starting at right changes the packet once, then repeats at left.
-- Every designated UB exit is unreachable from this native silent cycle.
private def cycle : Table sig Loop :=
  ⟨0, fun i => by obtain rfl := Fin.eq_zero i; exact .jump 0 (.inl .unit), fun _ => true⟩

private def finish (selected : Bool) : GuardedTable sig Loop :=
  ⟨0, fun _ => .exit 0, fun _ => selected⟩

private def unused : Primitives Op 1 := fun _ _ _ => .diverge
private def startRight (_ : Payload UnitTy) := rightBit

example : cycle.resolve Loop.length cycle.entry = none := rfl

example : cycle.head? cycle.native rightBit ⟨0, rightBit⟩ = some .diverge := rfl

example : cycle.normalize.head rightBit ⟨0, rightBit⟩ = .diverge := rfl

example : (cycle.normalize.head rightBit ⟨0, rightBit⟩).query? (0 : Fin 1) = none := rfl

private def twoBlockCycle : Table sig Packets where
  entry := 0
  row := Fin.cases (motive := fun i => Row sig Packets [Packets.get i, Bit])
    (.jump 1 (.var 0)) (fun i => by
      obtain rfl := Fin.eq_zero i
      exact .jump 0 (.inr .unit))
  selected _ := false

example : cycle.cutoff twoBlockCycle callers startRight startRight replyPackets single inventory = 1 := rfl

example : cycle.checkEntries? twoBlockCycle cycle.native twoBlockCycle.native
    callers startRight startRight replyPackets single inventory = some true := rfl

example : cycle.checkEntries? (Table.ofGuarded (finish false)) cycle.native (finish false).native
    callers startRight startRight replyPackets single single = some false := rfl

example : cycle.checkEntries? (Table.ofGuarded (finish true)) cycle.native (finish true).native
    callers startRight startRight replyPackets single single = some true := rfl

example : (Table.ofGuarded (finish true)).checkEntries? cycle (finish true).native cycle.native
    callers startRight startRight replyPackets single single = some false := rfl

-- The packed-row emitter does not admit this original let-bound region.
private def unsupported : CFG.Dependent.Native.Typed Op [Bit] TwoRequest.Exits :=
  ⟨.let₁ .unit (.br 0 .unit), .let₁ .unit (.br (ℓ := 0) rfl .unit)⟩

example : cycle.head? unsupported rightBit ⟨0, rightBit⟩ = none := rfl

example : cycle.checkEntries? twoBlockCycle unsupported twoBlockCycle.native
    callers startRight startRight replyPackets single inventory = none := rfl

private noncomputable def cycleObserved :=
  Shape.denote (withExitUB cycle.native cycle.selected) (model unused (cycle.visible.bindings rightBit)) 0

private noncomputable def finishObserved (selected : Bool) :=
  Shape.denote (withExitUB (finish selected).native (finish selected).selected)
    (model unused ((finish selected).bindings rightBit)) 0

private theorem cycle_diverges : cycleObserved = TwoRequest.resultBehaviour (.diverge : Result 2 1) :=
  cycle.exhausts_observes cycle.native rfl rightBit unused 0 rfl

private theorem finish_observes (selected : Bool) :
    finishObserved selected = TwoRequest.resultBehaviour (if selected then .ub else .ret 0 0) :=
  ((finish selected).observe_entry (finish selected).native (by cases selected <;> rfl) rightBit unused 0).trans
    ((finish selected).observe_step rightBit unused ⟨0, rightBit⟩ 0)

example : cycleObserved ≤ finishObserved true ∧ ¬ finishObserved true ≤ cycleObserved ∧
    ¬ cycleObserved ≤ finishObserved false := by
  rw [cycle_diverges, finish_observes true, finish_observes false]
  simp [TwoRequest.result_order, Result.refines]

private def requestThenCycle : Table sig Packets where
  entry := 0
  row := Fin.cases (motive := fun i => Row sig Packets [Packets.get i, Bit])
    (.guarded (request (.var 0))) (fun i => by
      obtain rfl := Fin.eq_zero i
      exact .jump 1 (.var 0))
  selected _ := false

private def requestThenExit : Table sig Packets where
  entry := 0
  row := Fin.cases (motive := fun i => Row sig Packets [Packets.get i, Bit])
    (.guarded (request (.var 0))) (fun _ => .guarded (.exit 0))
  selected _ := false

example : requestThenCycle.cutoff requestThenExit callers decode decode replyPackets inventory inventory = 3 := rfl

-- At a pending request, a primitive fault separates the two directions
-- even when a primitive divergence answer would agree with the silent loop.
example : cycle.checkEntries? requestThenExit cycle.native requestThenExit.native
    callers startRight decode replyPackets single inventory = some false := rfl

example : requestThenExit.checkEntries? cycle requestThenExit.native cycle.native
    callers decode startRight replyPackets inventory single = some false := rfl

private theorem tail_diverges :
    Shape.denote (withExitUB requestThenCycle.native requestThenCycle.selected)
      (model prim (requestThenCycle.visible.bindings leftBit)) 0 = TwoRequest.resultBehaviour .diverge := by
  let g := requestThenCycle.normalize
  refine (requestThenCycle.normalize_observes requestThenCycle.native rfl leftBit prim 0).trans
    ((g.observe_entry g.native rfl leftBit prim 0).trans ?_)
  exact (g.observe_step leftBit prim ⟨0, leftBit⟩ 0).trans (g.observe_step leftBit prim ⟨1, rightBit⟩ 1)

private theorem tail_returns :
    Shape.denote (withExitUB requestThenExit.native requestThenExit.selected)
      (model prim (requestThenExit.visible.bindings leftBit)) 0 = TwoRequest.resultBehaviour (.ret 0 1) := by
  let g := requestThenExit.normalize
  refine (requestThenExit.normalize_observes requestThenExit.native rfl leftBit prim 0).trans
    ((g.observe_entry g.native rfl leftBit prim 0).trans ?_)
  exact (g.observe_step leftBit prim ⟨0, leftBit⟩ 0).trans (g.observe_step leftBit prim ⟨1, rightBit⟩ 1)

example : requestThenCycle.checkEntries? requestThenExit requestThenCycle.native requestThenExit.native
    callers decode decode replyPackets inventory inventory = some false := by
  apply (Table.checkEntries_rejects_iff.{0,0} rfl rfl).mpr
  intro valid
  have impossible := valid (Fin 2) unitPacket prim 0
  change Shape.denote (withExitUB requestThenCycle.native requestThenCycle.selected)
      (model prim (requestThenCycle.visible.bindings leftBit)) 0 ≤
    Shape.denote (withExitUB requestThenExit.native requestThenExit.selected)
      (model prim (requestThenExit.visible.bindings leftBit)) 0 at impossible
  rw [tail_diverges, tail_returns, TwoRequest.result_order] at impossible
  simp [Result.refines] at impossible

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent
