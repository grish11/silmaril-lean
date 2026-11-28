module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile.CaptureDemand.Defs

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.CaptureDemand

open Silmaril.Isotope Silmaril.Isotope.Bridge.NamedFlat.Entry
open Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse
open Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.CaptureDemand
open Silmaril.SSA.LambdaRTL Silmaril.SSA.LambdaRTL.CFG.Cyclic
open Silmaril.Semantics.Dataflow.FiniteHeight (HeightBound)
open LambdaSSA.Semantics.Interaction.Typed.Ordered

universe u v w

section Analysis

variable {V K : Type w} {F : Type v} {n : Nat} [DecidableEq V] [DecidableEq K]
  (graph : CFG V K F) (names : Fin n → V)

private theorem infer_mem (i : Fin graph.blocks.length) (slot : Fin n) :
    slot ∈ infer graph names i ↔ (i, slot) ∈ solution graph names :=
  ⟨fun h => (Finset.mem_filter.mp h).2, fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩

theorem infer_closed : Closed graph names (infer graph names) := by
  have fixed : transfer graph names (solution graph names) = solution graph names :=
    (HeightBound.finset (Fin graph.blocks.length × Fin n)).solve_fixed (transfer graph names)
  intro i
  refine ⟨fun slot reads => ?_, fun target edge slot needed => ?_⟩
  · exact (infer_mem graph names i slot).mpr
      (fixed ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl reads⟩)
  · exact (infer_mem graph names i slot).mpr
      (fixed ▸ Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, Or.inr ⟨target, edge, (infer_mem graph names target slot).mp needed⟩⟩)

theorem infer_le {live : Fin graph.blocks.length → Finset (Fin n)} (closed : Closed graph names live) :
    infer graph names ≤ live := by
  let upper := Finset.univ.filter fun cell : Fin graph.blocks.length × Fin n => cell.2 ∈ live cell.1
  have prefixed : transfer graph names upper ≤ upper := by
    intro cell found
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rcases (Finset.mem_filter.mp found).2 with reads | ⟨target, edge, needed⟩
    · exact (closed cell.1).1 reads
    · exact (closed cell.1).2 target edge (Finset.mem_filter.mp needed).2
  have includes : solution graph names ≤ upper :=
    (HeightBound.finset (Fin graph.blocks.length × Fin n)).solve_le_of_prefixed (transfer graph names) prefixed
  intro i slot needed
  exact (Finset.mem_filter.mp (includes ((infer_mem graph names i slot).mp needed))).2

theorem noShadow_iff :
    (∃ live, Closed graph names live ∧ NoShadow graph names live) ↔ NoShadow graph names (infer graph names) := by
  constructor
  · rintro ⟨live, closed, valid⟩ i slot needed
    exact valid i slot (infer_le graph names closed i needed)
  · exact fun valid => ⟨_, infer_closed graph names, valid⟩

theorem infer_empty_of_packetClosed (closed : RoundTrip.PacketClosed graph) :
    infer graph names = fun _ => ∅ := by
  apply le_antisymm (infer_le graph names ?_) bot_le
  intro i
  refine ⟨?_, fun _ _ => le_rfl⟩
  intro slot member
  obtain ⟨distinct, reads⟩ := (Finset.mem_filter.mp member).2
  exact (distinct (Finset.mem_singleton.mp (closed _ (List.getElem_mem i.isLt) reads))).elim

end Analysis

section Reference

variable {κ K : Type (u + 1)} {n blocks : Nat} [DecidableEq K]
  {P : FlatInstitution.Signature.{u, v} κ}
  {context : BoundCtx (Ty κ) n} {exits : List K} {external : Fin exits.length → Ty κ}
  {fields : K → List (Register × Ty κ)}
  {code : LambdaSSA.FiniteCFG P.Instr blocks exits.length n}

variable (a : Lowered (numberedInterface context exits external) fields code)

local notation "attached" => withLiveOut (P := P) fields a.source
local notation "versioned" => Versioning.compile attached

private theorem map_toSlot (regs : List Register.{u}) (within : ∀ reg ∈ regs, reg.down < n) :
    ((regs.filterMap (toSlot n)).map fun j => (⟨j.val⟩ : Register.{u})) = regs := by
  induction regs with
  | nil => rfl
  | cons reg rest ih =>
    have first : toSlot n reg = some ⟨reg.down, within reg (by simp)⟩ := by simp [toSlot, within reg (by simp)]
    have tail := ih (fun j h => within j (List.mem_cons_of_mem _ h))
    simp [first, tail]

theorem reference_layout (within : a.SavesCaptures) (i : Fin (versioned).blocks.length) :
    a.savedRegisters i = (referenceLayouts a i).map (fun j => (⟨j.val⟩ : Register)) :=
  (map_toSlot _ (within i)).symm

theorem reference_projection (i : Fin (versioned).blocks.length) :
    List.Sublist (referenceLayouts a i) (referenceEntry a) := by
  let row : Fin (attached).blocks.length := Fin.cast (List.length_map _) i
  let keeps : Register → Bool := fun reg => decide (reg ≠ (attached).blocks[row].2.param)
  let used : Register → Bool := fun reg =>
    decide (∃ j : Fin (attached).blocks.length, reg ≠ (attached).blocks[j].2.param)
  let support := Versioning.registers attached
  have filter : (support.filter used).filter keeps = support.filter keeps := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro reg _
    by_cases allowed : reg ≠ (attached).blocks[row].2.param
    · have rowKeeps : keeps reg = true := decide_eq_true allowed
      have anyKeeps : used reg = true :=
        decide_eq_true (show ∃ j : Fin (attached).blocks.length, reg ≠ (attached).blocks[j].2.param from ⟨row, allowed⟩)
      simp [rowKeeps, anyKeeps]
    · have rowDrops : keeps reg = false := decide_eq_false allowed
      simp [rowDrops]
  have sublist : List.Sublist (support.filter keeps) (support.filter used) :=
    filter ▸ List.filter_sublist
  exact sublist.filterMap (toSlot n)

theorem ordered_installed_iff (entry : List (Fin n)) :
    (∀ i, a.savedRegisters i =
      (ordered attached (fun j : Fin n => (⟨j.val⟩ : Register)) entry
        (Fin.cast (List.length_map _) i)).map (fun j => (⟨j.val⟩ : Register))) ↔
    ∀ i : Fin (versioned).blocks.length, ∀ reg ∈ Versioning.registers attached,
      reg = (attached).blocks[Fin.cast (List.length_map _) i].2.param := by
  simp [ordered, infer_empty_of_packetClosed attached _ a.closed, Lowered.savedRegisters,
    Versioning.slots, List.filter_eq_nil_iff]

end Reference

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.CaptureDemand
