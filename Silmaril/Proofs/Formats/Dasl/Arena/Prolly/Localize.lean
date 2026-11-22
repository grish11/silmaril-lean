module

public import Silmaril.Formats.Dasl.Arena.Prolly.Localize.Defs
import Silmaril.Formats.Dasl.Arena.Prolly.Index.Thms

public section

namespace Silmaril.Proofs.Formats.Dasl.Arena.Prolly.Localize

open Silmaril.Formats.Dasl.Arena.Prolly
open Silmaril.Formats.Dasl.Arena.Prolly.Localize (Table childNames mapReadFault)
open Silmaril.Formats.Dasl.Prolly (route scan)
open Silmaril.Semantics (OrderedMap)
open Silmaril.Semantics.Prolly (Block selectChild)

variable {Name Key Payload : Type}
variable {source : Reader Name Key Payload} {before after : Table Name Key Payload}

theorem empty_valid : (Table.empty (Name := Name) (Key := Key) (Payload := Payload)).Valid source := by
  refine ⟨by simp [Table.empty], ?_, by simp [Table.empty], ?_⟩ <;> simp [Table.empty, Indexed.empty]

theorem extends_refl (table : Table Name Key Payload) : table.Extends table :=
  ⟨fun _ _ proof => proof, fun _ _ proof => proof, fun _ _ proof => proof⟩

theorem extends_trans {later : Table Name Key Payload} (first : before.Extends after) (second : after.Extends later) :
    before.Extends later :=
  ⟨fun _ _ hit => second.hits (first.hits hit), fun _ _ hit => second.origins (first.origins hit),
    fun _ _ hit => second.blocks (first.blocks hit)⟩

private theorem present {index : Nat} {block : Block (Handle Name) Key Payload}
    (read : before.arena.blocks[index]? = some block) : index < before.arena.blocks.size :=
  (Array.getElem?_eq_some_iff.mp read).choose

private theorem localize_frame (extension : before.Extends after) {block : Block Name Key Payload}
    (covered : Table.Covered before.locate block) :
    Indexed.localize after.locate block = Indexed.localize before.locate block := by
  cases block with
  | leaf entries => rfl
  | branch level children =>
    simp only [Indexed.localize, relabel, Block.branch.injEq, true_and]
    apply List.map_congr_left
    intro child member
    obtain ⟨index, hit⟩ := covered child.2 (List.mem_map_of_mem member)
    rw [hit, extension.hits hit]

private theorem write_spec [DecidableEq Name] {name : Name} {block : Block Name Key Payload}
    {arena : Indexed Name Key Payload} {index : Nat} (valid : before.Valid source)
    (miss : before.locate name = none) (read : source name = .ok block) (covered : Table.Covered before.locate block)
    (appended : before.arena.append? (Indexed.localize before.locate block) = some (arena, index)) :
    (before.write name arena index).Valid source ∧ before.Extends (before.write name arena index) ∧
      (before.write name arena index).locate name = some index := by
  obtain ⟨fresh, newRead, unchanged⟩ := Indexed.append_spec appended
  have oldIndex {oldName : Name} {old : Nat} (hit : before.locate oldName = some old) : old ≠ index := by
    obtain ⟨oldBlock, _, stored, _⟩ := valid.installed _ _ hit
    exact fresh ▸ Nat.ne_of_lt (present stored)
  have oldName {oldName : Name} {old : Nat} (hit : before.locate oldName = some old) : oldName ≠ name := by
    rintro rfl
    simp [miss] at hit
  have extension : before.Extends (before.write name arena index) := by
    refine ⟨fun _ _ hit => ?_, fun _ _ hit => ?_, fun _ _ hit => ?_⟩
    · simpa [Table.write, oldName hit] using hit
    · simpa [Table.write, oldIndex ((valid.inverse _ _).mpr hit)] using hit
    · exact (unchanged _ (fresh ▸ Nat.ne_of_lt (present hit))).trans hit
  refine ⟨⟨?_, ?_, ?_, ?_⟩, extension, by simp [Table.write]⟩
  · intro query other
    by_cases sameName : query = name <;> by_cases sameIndex : other = index
    · simp [Table.write, sameName, sameIndex]
    · subst query
      have notOrigin : before.origin other ≠ some name := fun hit => by
        have old := (valid.inverse name other).mpr hit
        simp [miss] at old
      simp [Table.write, sameIndex, Ne.symm sameIndex, notOrigin]
    · have notLocated : before.locate query ≠ some index := fun hit => oldIndex hit rfl
      simp [Table.write, sameName, Ne.symm sameName, sameIndex, notLocated]
    · simp [Table.write, sameName, sameIndex, valid.inverse]
  · intro other inside
    by_cases same : other = index
    · exact ⟨name, by simp [Table.write, same]⟩
    · change other < arena.blocks.size at inside
      have stored := Array.getElem?_eq_getElem inside
      rw [unchanged _ same] at stored
      obtain ⟨query, found⟩ := valid.domain _ (present stored)
      exact ⟨query, extension.origins found⟩
  · intro query other hit
    by_cases same : query = name
    · subst query
      have eq : index = other := by simpa [Table.write] using hit
      subst other
      exact ⟨block, read, (localize_frame extension covered).symm ▸ newRead, fun child mem =>
        (covered child mem).imp fun _ hit => extension.hits hit⟩
    · have oldHit : before.locate query = some other := by simpa [Table.write, same] using hit
      obtain ⟨oldBlock, oldRead, stored, oldCovered⟩ := valid.installed _ _ oldHit
      exact ⟨oldBlock, oldRead, (localize_frame extension oldCovered).symm ▸ extension.blocks stored,
        fun child mem => (oldCovered child mem).imp fun _ hit => extension.hits hit⟩
  · intro other found stored
    change arena.blocks[other]? = some found at stored
    by_cases same : other = index
    · subst other
      have eq := Option.some.inj (stored.symm.trans newRead)
      subst found
      rw [fresh]
      unfold Indexed.append? at appended
      split at appended
      · assumption
      · contradiction
    · exact valid.backward _ _ ((unchanged _ same).symm ▸ stored)

theorem add_spec [DecidableEq Name] {name : Name} (valid : before.Valid source)
    (added : before.add source name = .ok after) :
    after.Valid source ∧ before.Extends after ∧ ∃ index, after.locate name = some index := by
  cases hit : before.locate name with
  | some index =>
    have eq : before = after := by simpa [Table.add, hit] using added
    subst after
    exact ⟨valid, extends_refl _, index, hit⟩
  | none =>
    cases read : source name with
    | error fault => simp [Table.add, hit, read, Except.mapError, Bind.bind, Except.bind] at added
    | ok block =>
      by_cases planned : (childNames block).all (fun child => (before.locate child).isSome) = true
      · cases appended : before.arena.append? (Indexed.localize before.locate block) with
        | none => simp [Table.add, hit, read, Except.mapError, Bind.bind, Except.bind, planned, appended, -List.all_eq_true] at added
        | some pair =>
          obtain ⟨arena, index⟩ := pair
          have eq : before.write name arena index = after := by
            simpa [Table.add, hit, read, Except.mapError, Bind.bind, Except.bind, planned, appended, -List.all_eq_true] using added
          subst after
          have covered : Table.Covered before.locate block := by
            intro child member
            exact Option.isSome_iff_exists.mp (List.all_eq_true.mp planned child member)
          obtain ⟨valid, extension, found⟩ := write_spec valid hit read covered appended
          exact ⟨valid, extension, index, found⟩
      · simp [Table.add, hit, read, Except.mapError, Bind.bind, Except.bind, planned, -List.all_eq_true] at added

theorem install_spec [DecidableEq Name] {schedule : List Name} (valid : before.Valid source)
    (done : Table.install source schedule before = .ok after) :
    after.Valid source ∧ before.Extends after ∧ ∀ name ∈ schedule, ∃ index, after.locate name = some index := by
  induction schedule generalizing before with
  | nil =>
    have eq : before = after := Except.ok.inj done
    subst before
    exact ⟨valid, extends_refl _, by simp⟩
  | cons name rest ih =>
    cases added : before.add source name with
    | error fault => simp [Table.install, added, Except.bind] at done
    | ok middle =>
      obtain ⟨validMiddle, initial, index, hit⟩ := add_spec valid added
      obtain ⟨validAfter, final, scheduled⟩ := ih validMiddle (by simpa [Table.install, added, Except.bind] using done)
      refine ⟨validAfter, extends_trans initial final, ?_⟩
      simp only [List.mem_cons]
      rintro query (rfl | member)
      · exact ⟨index, final.hits hit⟩
      · exact scheduled query member

theorem checkedRoot_spec [DecidableEq Name] [LinearOrder Key] {width fuel index : Nat} {root : Name}
    {schedule : List Name} (valid : before.Valid source)
    (done : before.checkedRoot source width fuel root schedule = .ok (after, index)) :
    after.Valid source ∧ before.Extends after ∧ after.locate root = some index ∧
      ∃ entries map, scan source width fuel none root = .ok entries ∧ OrderedMap.ofEntries? entries = some map := by
  cases scanned : scan source width fuel none root with
  | error fault => simp [Table.checkedRoot, scanned, Except.mapError, Bind.bind, Except.bind] at done
  | ok entries =>
    cases ordered : OrderedMap.ofEntries? entries with
    | none => simp [Table.checkedRoot, scanned, ordered, Except.mapError, Bind.bind, Except.bind] at done
    | some map =>
      cases installed : Table.install source schedule before with
      | error fault => simp [Table.checkedRoot, scanned, ordered, installed, Except.mapError, Bind.bind, Except.bind] at done
      | ok table =>
        cases found : table.locate root with
        | none => simp [Table.checkedRoot, scanned, ordered, installed, found, Except.mapError, Bind.bind, Except.bind] at done
        | some other =>
          have eq : table = after ∧ other = index := by
            simpa [Table.checkedRoot, scanned, ordered, installed, found, Except.mapError, Bind.bind, Except.bind] using done
          obtain ⟨rfl, rfl⟩ := eq
          obtain ⟨validAfter, extension, _⟩ := install_spec valid installed
          exact ⟨validAfter, extension, found, entries, map, rfl, ordered⟩

theorem forward (valid : after.Valid source) :
    (after.installedReader source).Refines after.handle (after.arena.read source) := by
  intro name block read
  cases hit : after.locate name with
  | none => simp [Table.installedReader, hit] at read
  | some index =>
    obtain ⟨known, readKnown, stored, _⟩ := valid.installed _ _ hit
    have eq : known = block := Except.ok.inj (readKnown.symm.trans (by simpa [Table.installedReader, hit] using read))
    subst known
    simp [Table.handle, hit, Indexed.read, stored, Indexed.localize]
    rfl

theorem reverse (valid : after.Valid source) (fallback : Name) :
    (after.arena.read source).Refines (after.project fallback) source := by
  intro handle block read
  cases handle with
  | external name =>
    cases named : source name with
    | ok known =>
      have eq : relabel Handle.external known = block := by simpa [Indexed.read, named] using read
      subst block
      cases known <;> simpa [Table.project, relabel, List.map_map, Function.comp_def] using named
    | error fault => cases fault <;> simp [Indexed.read, named] at read
  | «local» index =>
    cases found : after.arena.blocks[index]? with
    | none => simp [Indexed.read, found] at read
    | some localBlock =>
      have eq : localBlock = block := by simpa [Indexed.read, found] using read
      subst localBlock
      obtain ⟨name, origin⟩ := valid.domain index (present found)
      obtain ⟨known, named, stored, _⟩ := valid.installed _ _ ((valid.inverse _ _).mpr origin)
      have eq : block = Indexed.localize after.locate known := Option.some.inj (found.symm.trans stored)
      subst block
      rw [Indexed.localize_relabel _ _ (fun _ => rfl) (fun name index hit => by
        simp [Table.project, (valid.inverse name index).mp hit])]
      simpa [Table.project, origin] using named

theorem route_agrees [LinearOrder Key] (valid : after.Valid source) (width fuel : Nat) (key : Key)
    {expected : Option Nat} {name : Name} {index : Nat} (hit : after.locate name = some index) :
    route (after.arena.read source) width key fuel expected (.local index) =
      (route source width key fuel expected name).mapError (mapReadFault after.handle) := by
  have root : after.handle name = .local index := by simp [Table.handle, hit]
  rw [← root]
  clear root
  suffices agrees : ∀ fuel expected name, (∃ index, after.locate name = some index) →
      route (after.arena.read source) width key fuel expected (after.handle name) =
        (route source width key fuel expected name).mapError (mapReadFault after.handle) from
    agrees fuel expected name ⟨index, hit⟩
  clear hit index fuel expected name
  intro fuel expected name linked
  induction fuel generalizing name expected with
  | zero => simp [route, Except.mapError, mapReadFault]
  | succ fuel ih =>
    obtain ⟨index, located⟩ := linked
    obtain ⟨block, named, stored, covered⟩ := valid.installed _ _ located
    have localRead : after.arena.read source (after.handle name) = .ok (relabel after.handle block) := by
      simp [Table.handle, located, Indexed.read, stored]
      rfl
    cases block with
    | leaf entries =>
      simp only [route, named, localRead, Bind.bind, Except.bind, relabel]
      split <;> simp [Except.mapError, mapReadFault]
    | branch level children =>
      let remap := fun (child : Key × Name) => (child.1, after.handle child.2)
      have chosen : selectChild key (children.map remap) = (selectChild key children).map remap := by
        simp [selectChild, remap, Function.comp_def]
      simp only [route, named, localRead, Bind.bind, Except.bind, relabel, List.length_map, List.pairwise_map]
      split
      · rw [show selectChild key (children.map (fun child => (child.1, after.handle child.2))) =
          (selectChild key children).map remap from chosen]
        cases selected : selectChild key children with
        | none => rfl
        | some child =>
          have member : child ∈ children := List.mem_of_find?_eq_some selected
          exact ih _ _ (covered child.2 (List.mem_map_of_mem member))
      · rfl

end Silmaril.Proofs.Formats.Dasl.Arena.Prolly.Localize
