module

public import Silmaril.Formats.Dasl.Arena.Prolly.Index.Defs

public section

namespace Silmaril.Proofs.Formats.Dasl.Arena.Prolly.Index

open Silmaril.Formats.Dasl.Arena.Prolly
open Silmaril.Formats.Dasl.Prolly (route)
open Silmaril.Semantics.Prolly (Block selectChild)

variable {Name Key Payload Ref Target : Type}

theorem route_refines [LinearOrder Key] {source : Reader Ref Key Payload} {map : Ref → Target}
    {target : Reader Target Key Payload} (agrees : source.Refines map target) (width fuel : Nat) (key : Key)
    {expected : Option Nat} {ref : Ref} {result : Option Payload}
    (hit : route source width key fuel expected ref = .ok result) :
    route target width key fuel expected (map ref) = .ok result := by
  induction fuel generalizing ref expected with
  | zero => simp [route] at hit
  | succ fuel ih =>
    cases read : source ref with
    | error fault => simp [route, read, Bind.bind, Except.bind] at hit
    | ok block =>
      have namedRead := agrees read
      cases block with
      | leaf entries =>
        simp only [route, read, Bind.bind, Except.bind] at hit
        simp only [route, namedRead, relabel, Bind.bind, Except.bind]
        split at hit
        · rename_i checks; simpa [checks] using hit
        · contradiction
      | branch level children =>
        let remap := fun (child : Key × Ref) => (child.1, map child.2)
        have chosen : selectChild key (children.map remap) = (selectChild key children).map remap := by
          simp [selectChild, remap, Function.comp_def]
        simp only [route, read, Bind.bind, Except.bind] at hit
        simp only [route, namedRead, Bind.bind, Except.bind, relabel]
        change (if (expected = none ∨ expected = some level) ∧ 0 < level ∧ 0 < (children.map remap).length ∧
          (children.map remap).length ≤ width ∧ (children.map remap).Pairwise (fun left right => left.1 < right.1)
          then _ else _) = _
        simp only [List.length_map, List.pairwise_map, remap] at ⊢
        split at hit
        · rename_i checks
          simp [checks]
          rw [show selectChild key (children.map (fun child => (child.1, map child.2))) =
            (selectChild key children).map remap from chosen]
          cases selected : selectChild key children with
          | none =>
            simp only [selected, Option.map_none] at hit ⊢
            exact congrArg Except.ok (Except.ok.inj hit)
          | some child => exact ih (by simpa only [selected] using hit)
        · contradiction

theorem append_spec {arena next : Indexed Name Key Payload} {block : Block (Handle Name) Key Payload} {index : Nat}
    (appended : arena.append? block = some (next, index)) :
    index = arena.blocks.size ∧ next.blocks[index]? = some block ∧
      (∀ other, other ≠ index → next.blocks[other]? = arena.blocks[other]?) := by
  unfold Indexed.append? at appended
  split at appended
  · cases appended
    refine ⟨rfl, Array.getElem?_push_size, ?_⟩
    intro other different
    simp [Array.getElem?_push, different]
  · contradiction

theorem acquire_spec {arena next : Indexed Name Key Payload} {source : Reader Name Key Payload}
    {locate : Name → Option Nat} {name : Name} {index : Nat}
    (acquired : arena.acquire source locate name = .ok (some (next, index))) :
    ∃ block, source name = .ok block ∧ next.blocks[index]? = some (Indexed.localize locate block) := by
  cases read : source name with
  | error fault => simp [Indexed.acquire, Except.map, read] at acquired
  | ok block =>
    have appended : arena.append? (Indexed.localize locate block) = some (next, index) := by
      simpa [Indexed.acquire, Except.map, read] using acquired
    exact ⟨block, rfl, (append_spec appended).2.1⟩

theorem admissible_iff {bound level : Nat} {children : List (Key × Handle Name)} :
    Indexed.admissible bound (.branch (Payload := Payload) level children) = true ↔
      ∀ child ∈ children, Indexed.KnownBefore bound child.2 := by
  simp only [Indexed.admissible, List.all_eq_true]
  exact forall_congr' fun child => imp_congr_right fun _ => by cases child.2 <;> simp [Indexed.KnownBefore]

theorem append_local_live {arena next : Indexed Name Key Payload} {index level child : Nat} {key : Key}
    {children : List (Key × Handle Name)} (appended : arena.append? (.branch level children) = some (next, index))
    (member : (key, .local child) ∈ children) :
    ∃ block, arena.blocks[child]? = some block ∧ next.blocks[child]? = some block := by
  have ⟨fresh, _, unchanged⟩ := append_spec appended
  unfold Indexed.append? at appended
  split at appended
  · rename_i allowed
    have inside : child < arena.blocks.size := admissible_iff.mp allowed _ member
    exact ⟨arena.blocks[child], Array.getElem?_eq_getElem inside, by rw [unchanged _ (fresh ▸ Nat.ne_of_lt inside), Array.getElem?_eq_getElem inside]⟩
  · contradiction

theorem localize_relabel (locate : Name → Option Nat) (project : Handle Name → Name)
    (external : ∀ name, project (.external name) = name)
    (localName : ∀ name index, locate name = some index → project (.local index) = name)
    (block : Block Name Key Payload) : relabel project (Indexed.localize locate block) = block := by
  cases block with
  | leaf entries => rfl
  | branch level children =>
    simp only [Indexed.localize, relabel, List.map_map, Block.branch.injEq, true_and]
    conv_rhs => rw [← List.map_id children]
    apply List.map_congr_left
    intro child _
    cases hit : locate child.2 with
    | none => simp [hit, external]
    | some index => simp [hit, localName _ _ hit]

end Silmaril.Proofs.Formats.Dasl.Arena.Prolly.Index
