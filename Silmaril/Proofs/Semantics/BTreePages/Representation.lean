module

public import Silmaril.Semantics.BTreePages.Defs

public section
namespace Silmaril.Proofs.Semantics.BTreePages

open Silmaril.Semantics Silmaril.Semantics.BTree Silmaril.Semantics.BTreePages

universe u
variable {Key Value Id : Type} {Memory : Type u}
variable {layout : Layout Id} {tree : Tree Key Value}
variable {store : Page.Store Id (PageData Key Value Id) Memory}
variable {memory other : Memory}

theorem atPath_append (tree : Tree Key Value) (start suffix : Position) :
    atPath tree (start ++ suffix) = (atPath tree start).bind (atPath · suffix) := by
  induction start generalizing tree with
  | nil => rfl
  | cons slot rest ih =>
    obtain ⟨height, node⟩ := tree
    cases height with
    | zero => rfl
    | succ height =>
      simp only [List.cons_append, atPath, Option.bind_assoc]
      congr 1
      funext child
      exact ih ⟨height, child⟩

private theorem reached_of_pageAt {position : Position} {data : PageData Key Value Id}
    (found : pageAt layout tree position = some data) : atPath tree position ≠ none := by
  intro absent
  simp [pageAt, absent] at found

theorem mem_footprint_iff {page : Id} :
    Footprint layout tree page ↔
      ∃ position data, layout position = page ∧ pageAt layout tree position = some data := by
  constructor
  · rintro ⟨position, reached, rfl⟩
    cases found : atPath tree position with
    | none => exact (reached found).elim
    | some subtree => exact ⟨position, encode layout position subtree.height subtree.root, rfl, by simp [pageAt, found]⟩
  · rintro ⟨position, data, address, found⟩
    exact ⟨position, reached_of_pageAt found, address⟩

variable [LinearOrder Key]

theorem represents_congr (agree : AgreesOn store (Footprint layout tree) memory other) :
    Represents store layout tree memory ↔ Represents store layout tree other := by
  have slotEq : ∀ position data, pageAt layout tree position = some data →
      store.lookup memory (layout position) = store.lookup other (layout position) :=
    fun position data found => agree _ (mem_footprint_iff.mpr ⟨position, data, rfl, found⟩)
  constructor <;> rintro ⟨ok, read⟩ <;> refine ⟨ok, fun position data found => ?_⟩
  · rw [← slotEq position data found, read position data found]
  · rw [slotEq position data found, read position data found]

theorem represents_set_outside {page : Id} (outside : ¬ Footprint layout tree page)
    (value : Page.Slot (PageData Key Value Id)) :
    Represents store layout tree (store.set memory page value) ↔ Represents store layout tree memory := by
  apply represents_congr
  intro readPage inside
  exact store.lookup_set_other memory page readPage value (fun eq => outside (eq ▸ inside))

theorem represents_over [DecidableEq Id] (ok : WellFormed layout tree)
    (outside : Page.MapMemory Id (PageData Key Value Id)) :
    ∃ memory, Represents (Page.mapStore Id _) layout tree memory ∧
      AgreesOn (Page.mapStore Id _) (fun page => ¬ Footprint layout tree page) memory outside := by
  classical
  let memory : Page.MapMemory Id (PageData Key Value Id) := fun page =>
    if present : ∃ data position, layout position = page ∧ pageAt layout tree position = some data then
      .defined (Classical.choose present)
    else outside page
  refine ⟨memory, ⟨ok, ?_⟩, ?_⟩
  · intro position data found
    change memory (layout position) = .defined data
    unfold memory
    have present : ∃ value pos, layout pos = layout position ∧ pageAt layout tree pos = some value :=
      ⟨data, position, rfl, found⟩
    rw [dite_eq_left present]
    obtain ⟨pos, address, read⟩ := Classical.choose_spec present
    have same := ok.2 pos position (reached_of_pageAt read) (reached_of_pageAt found) address
    rw [same, found] at read
    exact congrArg Page.Slot.defined (Option.some.inj read).symm
  · intro page absent
    change memory page = outside page
    apply dite_eq_right
    rintro ⟨data, position, address, found⟩
    exact absent (mem_footprint_iff.mpr ⟨position, data, address, found⟩)

theorem shared_representation_iff [DecidableEq Id] {left right : Tree Key Value}
    {leftLayout rightLayout : Layout Id} (leftOK : WellFormed leftLayout left)
    (rightOK : WellFormed rightLayout right) (outside : Page.MapMemory Id (PageData Key Value Id)) :
    (∃ memory, Represents (Page.mapStore Id _) leftLayout left memory ∧
      Represents (Page.mapStore Id _) rightLayout right memory ∧
      AgreesOn (Page.mapStore Id _)
        (fun page => ¬ Footprint leftLayout left page ∧ ¬ Footprint rightLayout right page) memory outside) ↔
      Compatible leftLayout rightLayout left right := by
  constructor
  · rintro ⟨_, leftRep, rightRep, _⟩ leftPos rightPos leftData rightData leftRead rightRead address
    have eq := leftRep.2 leftPos leftData leftRead
    rw [address, rightRep.2 rightPos rightData rightRead] at eq
    exact (Page.Slot.defined.inj eq).symm
  · intro compatible
    obtain ⟨base, leftRep, baseOutside⟩ := represents_over leftOK outside
    obtain ⟨combined, rightRep, combinedOutside⟩ := represents_over rightOK base
    refine ⟨combined, ⟨leftOK, ?_⟩, rightRep, ?_⟩
    · intro position data found
      by_cases shared : Footprint rightLayout right (leftLayout position)
      · obtain ⟨rightPos, rightData, address, rightRead⟩ := mem_footprint_iff.mp shared
        rw [← address, rightRep.2 rightPos rightData rightRead,
          compatible position rightPos data rightData found rightRead address.symm]
      · exact (combinedOutside _ shared).trans (leftRep.2 position data found)
    · intro page absent
      exact (combinedOutside page absent.2).trans (baseOutside page absent.1)

end Silmaril.Proofs.Semantics.BTreePages
