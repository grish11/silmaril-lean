module

public import Silmaril.Formats.Dasl.Arena.Prolly.Sweep.Mark.Defs
public import Silmaril.Formats.Dasl.Arena.Prolly.Sweep.Thms

public section

namespace Silmaril.Proofs.Formats.Dasl.Arena.Prolly.Mark

open Silmaril.Formats.Dasl.Arena.Prolly
open Silmaril.Formats.Dasl.Arena.Prolly.Sweep
open Silmaril.Semantics.Prolly (Block)

variable {Name Key Payload : Type} {arena : Indexed Name Key Payload} {roots : List (Handle Name)}

private theorem mem_id {ref : Handle Name} {index : Nat} : localId ref = some index ↔ ref = .local index := by
  cases ref <;> simp [localId]

private theorem child_reachable {index child : Nat} (reachable : Reachable arena roots (.local index))
    (member : child ∈ localChildren arena index) : Reachable arena roots (.local child) := by
  cases seen : arena.blocks[index]? with
  | none => simp [localChildren, seen] at member
  | some block =>
    cases block with
    | leaf _ => simp [localChildren, seen] at member
    | branch level children =>
      have selected : child ∈ children.filterMap (fun edge => localId edge.2) := by
        simpa only [localChildren, seen] using member
      obtain ⟨edge, found, localEdge⟩ := List.mem_filterMap.mp selected
      exact mem_id.mp localEdge ▸ Reachable.child reachable seen found

private theorem step_mem {index other : Nat} {marked : List Nat} :
    other ∈ markStep arena index marked ↔ other ∈ marked ∨ (index ∈ marked ∧ other ∈ localChildren arena index) := by
  by_cases found : index ∈ marked <;> simp [markStep, found, or_comm]

private def Sound (arena : Indexed Name Key Payload) (roots : List (Handle Name)) (marked : List Nat) : Prop :=
  ∀ index ∈ marked, Reachable arena roots (.local index)

private theorem step_sound {index : Nat} {marked : List Nat} (sound : Sound arena roots marked) :
    Sound arena roots (markStep arena index marked) := by
  intro other member
  rcases step_mem.mp member with prior | ⟨parent, child⟩
  · exact sound other prior
  · exact child_reachable (sound index parent) child

private theorem below_sound (fuel : Nat) (marked : List Nat) (sound : Sound arena roots marked) :
    Sound arena roots (markBelow arena fuel marked) := by
  induction fuel generalizing marked with
  | zero => exact sound
  | succ fuel ih => exact ih _ (step_sound sound)

private theorem below_retains (arena : Indexed Name Key Payload) (fuel : Nat) (marked : List Nat) {index : Nat}
    (present : index ∈ marked) : index ∈ markBelow arena fuel marked := by
  induction fuel generalizing marked with
  | zero => exact present
  | succ fuel ih => exact ih _ (step_mem.mpr (Or.inl present))

private theorem roots_sound (arena : Indexed Name Key Payload) (roots : List (Handle Name)) :
    Sound arena roots (roots.filterMap localId) := by
  intro index member
  obtain ⟨ref, present, localRoot⟩ := List.mem_filterMap.mp member
  exact mem_id.mp localRoot ▸ Reachable.root present

private def ClosedAbove (arena : Indexed Name Key Payload) (fuel : Nat) (marked : List Nat) : Prop :=
  ∀ index, fuel ≤ index → index ∈ marked → ∀ child ∈ localChildren arena index, child ∈ marked

private theorem close (ready : Markable arena roots) (fuel : Nat) (marked : List Nat)
    (sound : Sound arena roots marked) (above : ClosedAbove arena fuel marked) :
    ClosedAbove arena 0 (markBelow arena fuel marked) := by
  induction fuel generalizing marked with
  | zero => exact above
  | succ fuel ih =>
    apply ih _ (step_sound sound)
    intro index lower member child edge
    have prior : index ∈ marked := by
      rcases step_mem.mp member with prior | ⟨parent, next⟩
      · exact prior
      · exact False.elim (Nat.not_lt_of_ge lower (ready.2 fuel (sound fuel parent) index next))
    by_cases pivot : index = fuel
    · subst index
      exact step_mem.mpr (Or.inr ⟨prior, edge⟩)
    · exact step_mem.mpr (Or.inl (above index (by omega) prior child edge))

theorem sound {index : Nat} (marked : index ∈ mark arena roots) : Reachable arena roots (.local index) :=
  below_sound _ _ (roots_sound arena roots) index marked

theorem checked (ready : Markable arena roots) : check arena roots (mark arena roots) = true := by
  have closedAll := close ready arena.blocks.size _ (roots_sound arena roots) (by
    intro index past member
    exact False.elim (Nat.not_lt_of_ge past (ready.1 index (roots_sound arena roots index member))))
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply List.all_eq_true.mpr
    intro ref present
    cases ref with
    | external _ => rfl
    | «local» index =>
      have marked := below_retains arena arena.blocks.size (roots.filterMap localId)
        (List.mem_filterMap.mpr ⟨.local index, present, rfl⟩)
      simpa [kept, mark] using marked
  · apply List.all_eq_true.mpr
    intro index member
    have live := ready.1 index (sound member)
    rw [getElem?_pos arena.blocks index live]
    change closed (mark arena roots) arena.blocks[index] = true
    cases shape : arena.blocks[index] with
    | leaf _ => rfl
    | branch level children =>
      apply List.all_eq_true.mpr
      intro edge present
      cases ref : edge.2 with
      | external _ => rfl
      | «local» child =>
        have stored : arena.blocks[index]? = some (.branch level children) := by
          rw [getElem?_pos arena.blocks index live, shape]
        have localEdge : child ∈ localChildren arena index := by
          simp only [localChildren, stored, List.mem_filterMap]
          exact ⟨edge, present, ref ▸ rfl⟩
        have retained : child ∈ mark arena roots := closedAll index (Nat.zero_le _) member child localEdge
        simpa [kept, ref] using retained

theorem exact_of_swept {index : Nat} {view : Collected Name Key Payload}
    (swept : markAndSweep? arena roots = some view) :
    index ∈ mark arena roots ↔ Reachable arena roots (.local index) := by
  refine ⟨sound, fun live => ?_⟩
  simpa [kept] using keep_reachable (sweep_spec swept).1 live

theorem collected_slot {view : Collected Name Key Payload}
    (swept : markAndSweep? arena roots = some view) (index : Nat)
    (live : index < arena.blocks.size) :
    (view.slots[index]? = some (some arena.blocks[index]) ↔ Reachable arena roots (.local index)) ∧
    (view.slots[index]? = some none ↔ ¬ Reachable arena roots (.local index)) := by
  have slot := (sweep_spec swept).2.2 index
  rw [getElem?_pos arena.blocks index live] at slot
  by_cases marked : index ∈ mark arena roots
  · have retained : view.slots[index]? = some (some arena.blocks[index]) := by simpa [marked] using slot
    simp [retained, (exact_of_swept swept).mp marked]
  · have unreachable := fun reached => marked ((exact_of_swept swept).mpr reached)
    have gone : view.slots[index]? = some none := by simpa [marked] using slot
    simpa [gone] using unreachable

end Silmaril.Proofs.Formats.Dasl.Arena.Prolly.Mark
