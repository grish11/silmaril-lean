module

public import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Commutative.Defs
import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Commutative

open Silmaril.SSA.SeaOfNodes.Diamond
open AddPhi.Rotate (Program)
open AddPhi.Rotate.Pair.Dispatch.Materialize (suffix)
open AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse
open AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Commutative
open Silmaril.SSA.SeaOfNodes.GVN (keepOrigin)
open Silmaril.SSA.SeaOfNodes.Pure.SubZero (model word)

variable {inputs : List (ValueSort Unit)} {sigs : List (List (Ty Unit))}
variable {p : Program inputs sigs [word]} {rep : EntryAdd p} {target : Program inputs sigs [word, word]}

theorem check_provenance (checked : Commutative.check p rep = true) (slot : Slot) :
    ∃ phi : SharedWord inputs sigs,
      (rep.key = addKey (.arg p.residual) phi ∨ rep.key = addKey phi (.arg p.residual)) ∧
      (p.diamond.arms slot).outputs.get .head = keepOrigin (p.diamond.arms slot).dataflow phi := by
  cases found : addOperands? rep.key with
  | none => simp [Commutative.check, found] at checked
  | some key =>
    obtain ⟨⟨lhs, rhs⟩, keyEq⟩ := key
    simp only [Commutative.check, found, Bool.and_eq_true] at checked
    have atSlot : Commutative.matchesAt p lhs rhs slot = true := by
      cases slot
      · exact checked.1
      · exact checked.2
    rcases Bool.or_eq_true_iff.mp atSlot with ordered | swapped
    · obtain ⟨capture, forwarded⟩ := matchesAt_exact ordered
      exact ⟨rhs, .inl (keyEq.trans (congrArg (fun wire => addKey wire rhs) capture)), forwarded⟩
    · obtain ⟨capture, forwarded⟩ := matchesAt_exact swapped
      exact ⟨lhs, .inr (keyEq.trans (congrArg (addKey lhs) capture)), forwarded⟩

theorem check_agrees (checked : Commutative.check p rep = true) : RepresentativeAgrees p rep := by
  intro entry slot
  obtain ⟨phi, oriented, forwarded⟩ := check_provenance checked slot
  have same := rep.read_key model entry PUnit.unit
  dsimp only
  rw [read_forwarded entry slot forwarded]
  rcases oriented with key | key
  · rw [key] at same
    exact same
  · rw [key] at same
    exact same.trans (BitVec.add_comm _ _)

theorem discover_eq_some_iff :
    discoverAndRewrite? p = some target ↔
      ∃ value rep, p.suffix = suffix .right value ∧
        findRepresentative? p = some rep ∧ target = emit p rep value := by
  constructor
  · intro accepted
    obtain ⟨matched, _, next⟩ := Option.bind_eq_some_iff.mp accepted
    obtain ⟨rep, found, output⟩ := Option.bind_eq_some_iff.mp next
    exact ⟨matched.val, rep, matched.property, found, (Option.some.inj output).symm⟩
  · rintro ⟨value, rep, shape, found, rfl⟩
    have hit : rightValue? (suffix .right value) = some ⟨value, rfl⟩ := rfl
    simp only [discoverAndRewrite?]
    generalize h : p.suffix = old
    rw [h] at shape
    subst old
    simp [hit, found]

end Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Commutative
