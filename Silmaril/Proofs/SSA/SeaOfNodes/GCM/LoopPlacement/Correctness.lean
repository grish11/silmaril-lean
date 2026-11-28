module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopPlacement.Defs
import Silmaril.SSA.SeaOfNodes.GCM.Discovery.Thms
import Silmaril.SSA.SeaOfNodes.GCM.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopPlacement

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.Pure (OpSignature)
open Silmaril.SSA.SeaOfNodes.GCM

variable {Op : OpSignature} {Label : List Width → Type} {Input Result : List Width}
variable {cfg : Cfg Op Label Input Result}

variable (tree : DominatorTree cfg) (loopDepth : BlockId Label → Nat) (blocks : List (Target Label))
variable (operands : List (Point Label)) (uses : List (Use Label))

private theorem selection {chosen : Point Label}
    (found : chooseLoopPlacement tree loopDepth blocks operands uses = some chosen) :
    ∃ shallow, (acceptedCuts tree blocks operands uses).minOn?
        (fun p => loopDepth p.block) = some shallow ∧
      ((acceptedCuts tree blocks operands uses).filter
        (fun p => decide (loopDepth p.block = loopDepth shallow.block))).maxOn?
        (fun p => (tree.address p.block).length) = some chosen := by
  unfold chooseLoopPlacement rankCuts at found
  cases shallow : (acceptedCuts tree blocks operands uses).minOn? (fun p => loopDepth p.block) with
  | none => simp [shallow] at found
  | some p => exact ⟨p, rfl, by simpa [shallow] using found⟩

theorem chooseLoopPlacement_sound {chosen : Point Label}
    (found : chooseLoopPlacement tree loopDepth blocks operands uses = some chosen) :
    chosen ∈ candidateCuts cfg blocks ∧ Legal cfg operands uses chosen := by
  obtain ⟨_, _, deepest⟩ := selection tree loopDepth blocks operands uses found
  have admitted := (List.mem_filter.mp (List.maxOn?_mem deepest)).1
  obtain ⟨member, checked⟩ := List.mem_filter.mp admitted
  exact ⟨member, checkPlacement_sound tree checked⟩

theorem chooseLoopPlacement_minimal {chosen other : Point Label}
    (found : chooseLoopPlacement tree loopDepth blocks operands uses = some chosen)
    (member : other ∈ candidateCuts cfg blocks)
    (checked : checkPlacement tree operands uses other = true) :
    loopDepth chosen.block ≤ loopDepth other.block ∧
      (loopDepth chosen.block = loopDepth other.block →
        (tree.address other.block).length ≤ (tree.address chosen.block).length) := by
  obtain ⟨shallow, shallowest, deepest⟩ := selection tree loopDepth blocks operands uses found
  have admitted : other ∈ acceptedCuts tree blocks operands uses := List.mem_filter.mpr ⟨member, checked⟩
  have sameDepth := of_decide_eq_true (List.mem_filter.mp (List.maxOn?_mem deepest)).2
  have least : loopDepth shallow.block ≤ loopDepth other.block := by
    simpa [shallowest] using
      List.apply_get_minOn?_le_of_mem (f := fun p => loopDepth p.block) admitted
  refine ⟨sameDepth ▸ least, ?_⟩
  intro equalDepth
  have atDepth : other ∈ (acceptedCuts tree blocks operands uses).filter
      (fun p => decide (loopDepth p.block = loopDepth shallow.block)) :=
    List.mem_filter.mpr ⟨admitted, decide_eq_true (equalDepth.symm.trans sameDepth)⟩
  simpa [deepest] using
    List.le_apply_get_maxOn?_of_mem (f := fun p => (tree.address p.block).length) atDepth

theorem chooseLoopPlacement_eq_none_iff :
    chooseLoopPlacement tree loopDepth blocks operands uses = none ↔
      discoverPlacement tree blocks operands uses = none := by
  have same : acceptedCuts tree blocks operands uses = [] ↔
      discoverPlacement tree blocks operands uses = none := by
    simp [acceptedCuts, discoverPlacement]
  rw [← same]
  unfold chooseLoopPlacement rankCuts
  cases shallowest : (acceptedCuts tree blocks operands uses).minOn? (fun p => loopDepth p.block) with
  | none =>
    have empty : acceptedCuts tree blocks operands uses = [] := by
      have h := List.isSome_minOn?_iff (f := fun p : Point Label => loopDepth p.block)
        (xs := acceptedCuts tree blocks operands uses)
      simpa [shallowest] using h
    simp [empty]
  | some shallow =>
    have member := List.minOn?_mem shallowest
    have sameDepth : shallow ∈ (acceptedCuts tree blocks operands uses).filter
        (fun p => decide (loopDepth p.block = loopDepth shallow.block)) :=
      List.mem_filter.mpr ⟨member, decide_eq_true rfl⟩
    have nonempty := List.ne_nil_of_mem member
    have someCut := Option.isSome_iff_ne_none.mp
      (List.isSome_maxOn?_of_mem (f := fun p => (tree.address p.block).length) sameDepth)
    simp [nonempty, someCut]

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopPlacement
