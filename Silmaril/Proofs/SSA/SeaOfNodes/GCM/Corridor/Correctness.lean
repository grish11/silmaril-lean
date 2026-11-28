module

public import Silmaril.SSA.SeaOfNodes.GCM.Corridor.Defs
import Silmaril.SSA.SeaOfNodes.GCM.Dominance.Thms
import Silmaril.SSA.SeaOfNodes.GCM.EarlyPlacement.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LatePlacement.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopForest.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopPlacement.Thms
import Silmaril.SSA.SeaOfNodes.GCM.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.Corridor

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.Pure (OpSignature)
open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.Corridor
open Silmaril.SSA.SeaOfNodes.GCM.Dominance
open Silmaril.SSA.SeaOfNodes.GCM.EarlyPlacement
open Silmaril.SSA.SeaOfNodes.GCM.LatePlacement

theorem mem_addresses_iff (early late address : List Nat) :
    address ∈ addresses early late ↔ List.IsPrefix early address ∧ List.IsPrefix address late := by
  by_cases ordered : List.IsPrefix early late
  · rw [addresses, ite_eq_left (List.isPrefixOf_iff_prefix.mpr ordered)]
    have orderedLength := ordered.length_le
    constructor
    · intro member
      obtain ⟨steps, present, rfl⟩ := List.mem_map.mp member
      have count := List.mem_range.mp present
      have fromLate : List.IsPrefix (late.take (late.length - steps)) late := List.take_prefix _ _
      refine ⟨List.prefix_of_prefix_length_le ordered fromLate ?_, fromLate⟩
      simp only [List.length_take]
      omega
    · rintro ⟨above, below⟩
      have low := above.length_le
      have high := below.length_le
      refine List.mem_map.mpr ⟨late.length - address.length, List.mem_range.mpr (by omega), ?_⟩
      rw [show late.length - (late.length - address.length) = address.length by omega]
      exact (List.prefix_iff_eq_take.mp below).symm
  · have rejected : ¬ early.isPrefixOf late = true := fun hit => ordered
      (List.isPrefixOf_iff_prefix.mp hit)
    rw [addresses, ite_eq_right rejected]
    exact ⟨fun member => (List.not_mem_nil member).elim,
      fun h => (ordered (h.1.trans h.2)).elim⟩

private theorem filter_flatMap_of_accept {B P : Type} {nodes : List B}
    (keep : B → Bool) (cuts : B → List P) (accept : P → Bool)
    (retained : ∀ block point, point ∈ cuts block → accept point = true → keep block = true) :
    ((nodes.filter keep).flatMap cuts).filter accept = (nodes.flatMap cuts).filter accept := by
  simp only [List.filter_flatMap]
  induction nodes with
  | nil => rfl
  | cons block rest ih =>
    by_cases selected : keep block = true
    · simp [selected, ih]
    · have rejected : (cuts block).filter accept = [] :=
        List.filter_eq_nil_iff.mpr fun point member accepted => selected
          (retained block point member accepted)
      simp [selected, rejected, ih]

variable {Op : OpSignature} {Label : List Width → Type} {Input Result : List Width}
variable {cfg : Cfg Op Label Input Result} {tree : DominatorTree cfg}
variable {blocks : List (Target Label)} {operands : List (Point Label)} {uses : List (Use Label)}
variable {early late : BlockId Label} {loops : List (LoopForest.HeaderLoop Label)}
variable [DecidableEq (Target Label)]

theorem acceptedCorridorCuts_eq (complete : tree.Complete) (closed : checkClosed cfg blocks = true)
    (earlyFound : earlyBound? tree operands = some early) (lateFound : lateBound? tree blocks uses = some late) :
    acceptedCorridorCuts tree blocks early late operands uses = acceptedCuts tree blocks operands uses := by
  unfold acceptedCorridorCuts acceptedCuts candidateCuts
  apply filter_flatMap_of_accept
  intro block point member accepted
  obtain ⟨cut, _, rfl⟩ := List.mem_map.mp member
  have legal := checkPlacement_sound tree accepted
  obtain ⟨valid, afterEarly, beforeLate, _⟩ :=
    (legal_iff_bounds complete closed earlyFound lateFound).mp legal
  have lateReachable := (lateBound?_spec complete closed lateFound).1
  exact decide_eq_true ((mem_addresses_iff ..).mpr
    ⟨complete.prefix_complete valid.1 afterEarly, complete.prefix_complete lateReachable beforeLate⟩)

private theorem forest_closed (admitted : LoopForest.forest? tree blocks = some loops) :
    checkClosed cfg blocks = true := by
  have inventory : NaturalLoop.checkInventory tree blocks = true := by
    by_cases valid : NaturalLoop.checkInventory tree blocks = true
    · exact valid
    · simp [LoopForest.forest?, LoopForest.loops?, LoopForest.discover?, valid] at admitted
  simp only [NaturalLoop.checkInventory, List.all_eq_true, Bool.and_eq_true] at inventory
  apply List.all_eq_true.mpr
  intro src listed
  apply List.all_eq_true.mpr
  rintro ⟨slot, dst⟩ member
  have inSlots : slot ∈ NaturalLoop.slots := by cases slot <;> decide
  have actual := mem_occurrences_iff.mp member
  have closed := (inventory src listed).2 slot inSlots
  exact decide_eq_true (by simpa [actual, NaturalLoop.vertices] using closed)

private theorem chooseInForest_eq (complete : tree.Complete) (closed : checkClosed cfg blocks = true) :
    chooseInForest tree loops blocks operands uses =
      chooseLoopPlacement tree (LoopForest.depth tree loops) blocks operands uses := by
  by_cases empty : uses = []
  · simp [chooseInForest, empty]
  have noPlacement (illegal : ∀ point ∈ candidateCuts cfg blocks, ¬ Legal cfg operands uses point) :
      chooseLoopPlacement tree (LoopForest.depth tree loops) blocks operands uses = none :=
    (chooseLoopPlacement_complete tree (LoopForest.depth tree loops) blocks operands uses complete).mpr illegal
  cases e : earlyBound? tree operands with
  | none =>
    have rejected := noPlacement (fun point _ legal => by
      have bound := (earlyBound?_isSome_iff complete).mpr
        ⟨fun operand member => (legal.operands_available operand member).1,
          point.block, legal.candidate_valid.1,
          fun operand member => (legal.operands_available operand member).2.dominates⟩
      simp [e] at bound)
    simp [chooseInForest, empty, e, rejected]
  | some early =>
    cases l : lateBound? tree blocks uses with
    | none =>
      have rejected := noPlacement (fun point _ legal => by
        have bound := (lateBound?_isSome_iff (blocks := blocks) complete).mpr
          ⟨empty, fun use member => by
            obtain ⟨read, resolved, valid, _⟩ := legal.uses_available use member
            exact ⟨read, resolved, valid⟩⟩
        simp [l] at bound)
      simp [chooseInForest, empty, e, l, rejected]
    | some late =>
      simp [chooseInForest, empty, e, l, acceptedCorridorCuts_eq complete closed e l,
        chooseLoopPlacement]

theorem choosePlacement_eq (complete : tree.Complete) :
    Corridor.choosePlacement tree blocks operands uses =
      LoopForest.choosePlacement tree blocks operands uses := by
  cases admitted : LoopForest.forest? tree blocks with
  | none => simp [Corridor.choosePlacement, LoopForest.choosePlacement, admitted]
  | some loops =>
    simpa [Corridor.choosePlacement, LoopForest.choosePlacement, admitted] using
      chooseInForest_eq (loops := loops) (operands := operands) (uses := uses)
        complete (forest_closed admitted)

theorem chooseSynthesized?_eq (number : BlockId Label → Nat) (injective : Function.Injective number) :
    chooseSynthesized? cfg blocks number injective operands uses =
      (Dominance.Tree.Synthesis.synthesize? cfg blocks number injective).bind fun tree =>
        LoopForest.choosePlacement tree.1 blocks operands uses := by
  unfold chooseSynthesized?
  cases computed : Dominance.Tree.Synthesis.synthesize? cfg blocks number injective with
  | none => rfl
  | some tree => exact choosePlacement_eq tree.2

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.Corridor
