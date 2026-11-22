module

public import Silmaril.Formats.Dasl.Arena.Prolly.Sweep.Defs

public section

namespace Silmaril.Proofs.Formats.Dasl.Arena.Prolly.Sweep

open Silmaril.Formats.Dasl.Arena.Prolly
open Silmaril.Formats.Dasl.Arena.Prolly.Sweep
open Silmaril.Formats.Dasl.Prolly (route)
open Silmaril.Semantics.Prolly (Block selectChild)

variable {Name Key Payload : Type} {arena : Indexed Name Key Payload}
variable {view : Collected Name Key Payload} {roots : List (Handle Name)} {indices : List Nat}

theorem sweep_spec (swept : sweep? arena roots indices = some view) :
    check arena roots indices = true ∧ view.slots.size = arena.blocks.size ∧
      ∀ index : Nat, view.slots[index]? =
        (arena.blocks[index]?).map (fun block => if indices.contains index then some block else none) := by
  unfold sweep? at swept
  split at swept
  · rename_i checked
    cases swept
    refine ⟨checked, by simp, ?_⟩
    intro index
    by_cases inside : index < arena.blocks.size
    · rw [Array.getElem?_ofFn, Array.getElem?_eq_getElem inside]
      simp [inside]
    · rw [Array.getElem?_ofFn, Array.getElem?_eq_none (Nat.le_of_not_lt inside)]
      simp [inside]
  · contradiction

private theorem kept_block (checked : check arena roots indices = true) {index : Nat}
    (keep : kept (Name := Name) indices (.local index) = true) :
    ∃ block, arena.blocks[index]? = some block ∧ closed indices block = true := by
  have marks := (Bool.and_eq_true_iff.mp checked).2
  have member : index ∈ indices := by simpa [kept] using keep
  have accepted := List.all_eq_true.mp marks index member
  cases found : arena.blocks[index]? with
  | none => simp [found] at accepted
  | some block => exact ⟨block, rfl, by simpa [found] using accepted⟩

theorem keep_reachable (checked : check arena roots indices = true)
    {ref : Handle Name} (reachable : Reachable arena roots ref) : kept indices ref = true := by
  induction reachable with
  | root member => exact List.all_eq_true.mp (Bool.and_eq_true_iff.mp checked).1 _ member
  | child _ read member parent =>
    obtain ⟨block, stored, stays⟩ := kept_block checked parent
    have eq := Option.some.inj (stored.symm.trans read)
    subst block
    exact List.all_eq_true.mp stays _ member

theorem read_kept (swept : sweep? arena roots indices = some view) (external : Reader Name Key Payload)
    {ref : Handle Name} (keep : kept indices ref = true) : view.read external ref = arena.read external ref := by
  cases ref with
  | external name => rfl
  | «local» index =>
    have member : index ∈ indices := by simpa [kept] using keep
    cases found : arena.blocks[index]? <;>
      simp [Collected.read, Indexed.read, (sweep_spec swept).2.2 index, member, found]

theorem route_kept [LinearOrder Key] (swept : sweep? arena roots indices = some view)
    (external : Reader Name Key Payload) (width fuel : Nat) (key : Key)
    {expected : Option Nat} {ref : Handle Name} (keep : kept indices ref = true) :
    route (view.read external) width key fuel expected ref = route (arena.read external) width key fuel expected ref := by
  have checked := (sweep_spec swept).1
  induction fuel generalizing expected ref with
  | zero => rfl
  | succ fuel ih =>
    have same := read_kept swept external keep
    cases found : arena.read external ref with
    | error fault => simp [route, same, found, Bind.bind, Except.bind]
    | ok block =>
      cases block with
      | leaf _ => simp [route, same, found, Bind.bind, Except.bind]
      | branch level children =>
        simp only [route, same, found, Bind.bind, Except.bind]
        split
        · cases selected : selectChild key children with
          | none => rfl
          | some child =>
            have member : child ∈ children := List.mem_of_find?_eq_some selected
            apply ih
            cases ref with
            | external name =>
              cases read : external name with
              | error fault => cases fault <;> simp [Indexed.read, read] at found
              | ok named =>
                cases named with
                | leaf _ => simp [Indexed.read, read, relabel] at found
                | branch namedLevel namedChildren =>
                  have shape : relabel Handle.external (.branch namedLevel namedChildren : Block Name Key Payload) =
                      .branch level children := by simpa [Indexed.read, read] using found
                  have eq : namedChildren.map (fun pair => (pair.1, Handle.external pair.2)) = children := by
                    exact (Block.branch.inj shape).2
                  rw [← eq] at member
                  obtain ⟨edge, _, rfl⟩ := List.mem_map.mp member
                  rfl
            | «local» index =>
              obtain ⟨block, stored, stays⟩ := kept_block checked keep
              have eq : block = .branch level children := by simpa [Indexed.read, stored] using found
              subst block
              exact List.all_eq_true.mp stays _ member
        · rfl

end Silmaril.Proofs.Formats.Dasl.Arena.Prolly.Sweep
