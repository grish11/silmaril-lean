module

public import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Defs
import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Elimination.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Equality.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse

open Silmaril.SSA.SeaOfNodes.Diamond
open AddPhi.Rotate (Program)
open AddPhi.Rotate.Pair.Dispatch.Materialize
open AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse
open Silmaril.SSA.SeaOfNodes.GVN (keepOrigin read_keepOrigin)
open Silmaril.SSA.SeaOfNodes.GVN.Elimination (Routing)
open Silmaril.SSA.SeaOfNodes.Pure.SubZero (model word wordPort)
open Silmaril.SSA.RVSDG (Origin Tuple Wires)

variable {inputs : List (ValueSort Unit)} {sigs : List (List (Ty Unit))}
variable {p : Program inputs sigs [word]} {rep : EntryAdd p} {target : Program inputs sigs [word, word]}

private theorem same_wire {T : Type} {args : List T} {past : List (List T)} {t : T}
    (lhs rhs : Origin args past t) (same : lhs.address = rhs.address) : lhs = rhs :=
  congrArg (fun (wires : Wires args past [t]) => wires.get .head)
    (Silmaril.SSA.RVSDG.NestedTheta.Equality.addresses_injective (.cons lhs .nil) (.cons rhs .nil)
      (congrArg (fun addr => [addr]) same))

private theorem forwards_exact {rhs : SharedWord inputs sigs} {slot : Slot}
    (checked : forwards p rhs slot = true) :
    (p.diamond.arms slot).outputs.get .head = keepOrigin (p.diamond.arms slot).dataflow rhs :=
  same_wire _ _ (of_decide_eq_true checked)

theorem matchesAt_exact {lhs rhs : SharedWord inputs sigs} {slot : Slot}
    (checked : matchesAt p lhs rhs slot = true) :
    lhs = .arg p.residual ∧
      (p.diamond.arms slot).outputs.get .head = keepOrigin (p.diamond.arms slot).dataflow rhs := by
  have ⟨capture, phi⟩ := Bool.and_eq_true_iff.mp checked
  exact ⟨same_wire _ _ (of_decide_eq_true capture), forwards_exact phi⟩

theorem check_provenance (accepted : check p rep = true) :
    ∃ rhs : SharedWord inputs sigs, rep.key = addKey (.arg p.residual) rhs ∧
      ∀ slot : Slot, ((p.diamond.arms slot).outputs.get .head) =
        keepOrigin (p.diamond.arms slot).dataflow rhs := by
  cases found : addOperands? rep.key with
  | none => simp [check, found] at accepted
  | some key =>
    obtain ⟨⟨lhs, rhs⟩, keyEq⟩ := key
    simp only [check, found, Bool.and_eq_true] at accepted
    obtain ⟨captureEq, first⟩ := matchesAt_exact accepted.1
    refine ⟨rhs, keyEq.trans (congrArg (fun wire => addKey wire rhs) captureEq), ?_⟩
    intro slot
    cases slot
    · exact first
    · exact forwards_exact accepted.2

theorem route_agrees (value x phi : BitVec 64) :
    let before : Tuple (Val model.value) OldArgs := .cons x (.cons phi .nil)
    let after : Tuple (Val model.value) NewArgs := .cons x (.cons (x + phi) (.cons phi .nil))
    route.AgreesBetween model before after
      ((suffix .right value).dataflow.eval model before PUnit.unit)
      ((shortened value).dataflow.eval model after PUnit.unit) := by
  dsimp only
  intro t wire
  cases wire with
  | arg port =>
    cases port with
    | head => rfl
    | tail port =>
      cases port with
      | head => rfl
      | tail invalid => cases invalid
  | output i port =>
    cases i using Fin.cases with
    | zero =>
      cases port with
      | head => rfl
      | tail invalid => cases invalid
    | succ i =>
      cases i using Fin.cases with
      | zero =>
        cases port with
        | head => rfl
        | tail invalid => cases invalid
      | succ i =>
        cases i using Fin.cases with
        | zero =>
          cases port with
          | head => rfl
          | tail invalid => cases invalid
        | succ invalid => exact invalid.elim0

theorem rewrite?_eq_some_iff :
    rewrite? p rep = some target ↔
      ∃ value, p.suffix = suffix .right value ∧ check p rep = true ∧ target = emit p rep value := by
  constructor
  · intro accepted
    obtain ⟨shape, _, emitted⟩ := Option.bind_eq_some_iff.mp accepted
    split at emitted
    · rename_i checked
      exact ⟨shape.val, shape.property, checked, (Option.some.inj emitted).symm⟩
    · contradiction
  · rintro ⟨value, shape, checked, rfl⟩
    have hit : rightValue? (suffix .right value) = some ⟨value, rfl⟩ := rfl
    simp only [rewrite?]
    generalize h : p.suffix = old
    rw [h] at shape
    subst old
    rw [hit]
    simp [checked]

private theorem arm_read (p : Program inputs sigs [word]) (slot : Slot)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    let arm := p.diamond.arms slot
    let shared := p.diamond.shared.eval model entry PUnit.unit
    (arm.eval model entry shared).get .head =
      read model (arm.outputs.get .head) entry (arm.dataflow.eval model entry shared) := by
  dsimp only [Arms.Arm.eval]
  generalize (p.diamond.arms slot).outputs = wires
  cases wires with
  | cons wire tail => cases tail; rfl

theorem read_forwarded {rhs : SharedWord inputs sigs}
    (entry : Tuple (Val model.value) (dataPorts inputs)) (slot : Slot) :
    ((p.diamond.arms slot).outputs.get .head) = keepOrigin (p.diamond.arms slot).dataflow rhs →
    let shared := p.diamond.shared.eval model entry PUnit.unit
    ((p.diamond.arms slot).eval model entry shared).get .head = read model rhs entry shared := by
  intro forwarded
  dsimp only
  erw [arm_read p slot entry, forwarded, read_keepOrigin]

theorem check_agrees (accepted : check p rep = true) : RepresentativeAgrees p rep := by
  intro entry slot
  obtain ⟨rhs, key, forwarded⟩ := check_provenance accepted
  have same := rep.read_key model entry PUnit.unit
  rw [key] at same
  dsimp only
  rw [read_forwarded entry slot (forwarded slot)]
  exact same

private theorem capture_eval (p : Program inputs sigs [word]) (rep : EntryAdd p)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (slot : Slot) :
    let shared := p.diamond.shared.eval model entry PUnit.unit
    ((capture p rep).arms slot).eval model entry shared =
      .cons (read model rep.origin entry shared) ((p.diamond.arms slot).eval model entry shared) := by
  let shared := p.diamond.shared.eval model entry PUnit.unit
  exact congrArg (fun v : BitVec 64 =>
    Tuple.cons (F := Val model.value) (t := wordPort) v ((p.diamond.arms slot).eval model entry shared))
    (read_keepOrigin (p.diamond.arms slot).dataflow rep.origin model entry shared)

private theorem singleton_eta (values : Tuple (Val model.value) [wordPort]) :
    values = .cons (values.get .head) .nil := by
  cases values with
  | cons _ tail => cases tail; rfl

theorem emit_agrees_of (agrees : RepresentativeAgrees p rep) (value : BitVec 64)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (slot : Slot) :
    let before := slotArgs p entry slot
    let after := slotArgs (emit p rep value) entry slot
    route.AgreesBetween model before after
      ((suffix .right value).dataflow.eval model before PUnit.unit)
      ((shortened value).dataflow.eval model after PUnit.unit) := by
  let shared := p.diamond.shared.eval model entry PUnit.unit
  let phi := ((p.diamond.arms slot).eval model entry shared).get .head
  let x := entry.get p.residual
  have row : (p.diamond.arms slot).eval model entry shared =
      Tuple.cons (F := Val model.value) (t := wordPort) phi .nil := singleton_eta _
  let before := Tuple.cons (F := Val model.value) (t := wordPort) x
    ((p.diamond.arms slot).eval model entry shared)
  let after := Tuple.cons (F := Val model.value) (t := wordPort) x
    (((capture p rep).arms slot).eval model entry shared)
  change route.AgreesBetween model before after
    ((suffix .right value).dataflow.eval model before PUnit.unit)
    ((shortened value).dataflow.eval model after PUnit.unit)
  dsimp only [before, after]
  rw [capture_eval, agrees entry slot, row]
  exact route_agrees value x phi

private theorem emit_slot_eq_of (agrees : RepresentativeAgrees p rep) {value : BitVec 64}
    (shape : p.suffix = suffix .right value)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (slot : Slot) :
    (emit p rep value).atSlot entry slot = p.atSlot entry slot := by
  change (shortened value).eval model (slotArgs (emit p rep value) entry slot) =
    p.suffix.eval model (slotArgs p entry slot)
  rw [shape]
  exact (emit_agrees_of agrees value entry slot _ (suffix .right value).result).symm

theorem rewrite?_slot_eq (accepted : rewrite? p rep = some target)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (slot : Slot) :
    target.atSlot entry slot = p.atSlot entry slot := by
  obtain ⟨value, shape, certified, rfl⟩ := rewrite?_eq_some_iff.mp accepted
  exact emit_slot_eq_of (check_agrees certified) shape entry slot

theorem emit_returns_iff_of (agrees : RepresentativeAgrees p rep) {value : BitVec 64}
    (shape : p.suffix = suffix .right value)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (returned : BitVec 64) :
    (emit p rep value).Returns entry returned ↔ p.Returns entry returned := by
  let slot := p.diamond.merge.slot
    (.ofBool (read model p.diamond.predicate entry (p.diamond.shared.eval model entry PUnit.unit)).down)
  rw [Program.returns_iff_denote, Program.returns_iff_denote]
  exact Iff.of_eq (congrArg (· = returned) (emit_slot_eq_of agrees shape entry slot))

end Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse
