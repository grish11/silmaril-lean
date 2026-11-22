module

public import Silmaril.Formats.Dasl.Arena.Prolly.CopyRoot.Defs
import Silmaril.Formats.Dasl.Arena.Prolly.Index.Thms

public section

namespace Silmaril.Proofs.Formats.Dasl.Arena.Prolly.CopyRoot

open Silmaril.Formats.Dasl.Arena.Prolly
open Silmaril.Formats.Dasl.Arena.Prolly.CopyRoot (Directory)
open Silmaril.Formats.Dasl.Prolly (route)
open Silmaril.Semantics.Prolly (Block selectChild)

variable {Root Name Key Payload : Type} {before after : Directory Root Name Key Payload}

theorem empty_valid : (Directory.empty (Root := Root) (Name := Name) (Key := Key) (Payload := Payload)).Valid := by
  constructor <;> simp [Directory.empty, Indexed.empty]

private theorem append_size {arena next : Indexed Name Key Payload} {block : Block (Handle Name) Key Payload} {index : Nat}
    (appended : arena.append? block = some (next, index)) : next.blocks.size = arena.blocks.size + 1 := by
  unfold Indexed.append? at appended
  split at appended
  · cases appended; simp
  · contradiction

theorem copy_spec [DecidableEq Root] {root : Root} {block : Block (Handle Name) Key Payload} {index : Nat}
    (valid : before.Valid) (copied : before.copy? root block = some (after, index)) :
    after.Valid ∧ index = before.arena.blocks.size ∧ after.roots root = some (.local index) ∧
      (∀ other ≠ root, after.roots other = before.roots other) ∧ after.arena.blocks[index]? = some block ∧
      ∀ other : Nat, other ≠ index → after.arena.blocks[other]? = before.arena.blocks[other]? := by
  cases appended : before.arena.append? block with
  | none => simp [Directory.copy?, appended, Bind.bind, Option.bind] at copied
  | some pair =>
    obtain ⟨arena, fresh⟩ := pair
    obtain ⟨atEnd, stored, oldReads⟩ := Indexed.append_spec appended
    have size := append_size appended
    have allowed : Indexed.admissible fresh block = true := by
      rw [atEnd]
      unfold Indexed.append? at appended
      split at appended
      · assumption
      · contradiction
    have eq : (⟨arena, fun query => if query = root then some (.local fresh) else before.roots query⟩ :
        Directory Root Name Key Payload) = after ∧ fresh = index := by
      simpa [Directory.copy?, appended, Bind.bind, Option.bind, Pure.pure] using copied
    obtain ⟨rfl, rfl⟩ := eq
    refine ⟨⟨?_, ?_⟩, atEnd, by simp, by simp +contextual, stored, oldReads⟩
    · intro other found read
      by_cases same : other = fresh
      · subst other
        have eq : found = block := Option.some.inj (read.symm.trans stored)
        subst found
        exact allowed
      · exact valid.backward _ _ ((oldReads _ same).symm ▸ read)
    · intro query ref hit
      by_cases same : query = root
      · have eq : Handle.local fresh = ref := by simpa [same] using hit
        subst ref
        simp [Indexed.KnownBefore, size, atEnd]
      · have old := valid.live query ref (by simpa [same] using hit)
        cases ref with
        | external _ => trivial
        | «local» _ => simp only [Indexed.KnownBefore, size] at old ⊢; omega

theorem read_frame {fresh : Nat} (atEnd : fresh = before.arena.blocks.size)
    (same : ∀ other : Nat, other ≠ fresh → after.arena.blocks[other]? = before.arena.blocks[other]?)
    (external : Reader Name Key Payload) {ref : Handle Name} (live : Indexed.KnownBefore before.arena.blocks.size ref) :
    after.arena.read external ref = before.arena.read external ref := by
  cases ref with
  | external _ => rfl
  | «local» index =>
    have different : index ≠ fresh := atEnd ▸ Nat.ne_of_lt live
    simp only [Indexed.read, same _ different]

private theorem reader_closed (valid : before.Valid) (external : Reader Name Key Payload) {ref : Handle Name}
    (live : Indexed.KnownBefore before.arena.blocks.size ref) {level : Nat} {children : List (Key × Handle Name)}
    (read : before.arena.read external ref = .ok (.branch level children)) {child : Key × Handle Name}
    (member : child ∈ children) : Indexed.KnownBefore before.arena.blocks.size child.2 := by
  cases ref with
  | «local» index =>
    cases stored : before.arena.blocks[index]? with
    | none => simp [Indexed.read, stored] at read
    | some block =>
      have eq : block = .branch level children := by simpa [Indexed.read, stored] using read
      subst block
      have prior := Indexed.admissible_iff.mp (valid.backward index _ stored) child member
      cases shape : child.2 with
      | external _ => trivial
      | «local» _ => exact Nat.lt_trans (by simpa [shape, Indexed.KnownBefore] using prior) live
  | external name =>
    cases stored : external name with
    | error fault => cases fault <;> simp [Indexed.read, stored] at read
    | ok block =>
      have eq : relabel Handle.external block = .branch level children := by simpa [Indexed.read, stored] using read
      cases block with
      | leaf _ => cases eq
      | branch _ named =>
        rw [← (Block.branch.inj eq).2] at member
        obtain ⟨edge, _, rfl⟩ := List.mem_map.mp member
        trivial

theorem route_frame [LinearOrder Key] (valid : before.Valid)
    (external : Reader Name Key Payload) (width fuel : Nat) (key : Key)
    (frame : ∀ ref, Indexed.KnownBefore before.arena.blocks.size ref →
      after.arena.read external ref = before.arena.read external ref)
    {expected : Option Nat} {ref : Handle Name} (live : Indexed.KnownBefore before.arena.blocks.size ref) :
    route (after.arena.read external) width key fuel expected ref =
      route (before.arena.read external) width key fuel expected ref := by
  induction fuel generalizing expected ref with
  | zero => rfl
  | succ fuel ih =>
    cases read : before.arena.read external ref with
    | error fault => simp [route, frame _ live, read, Bind.bind, Except.bind]
    | ok block =>
      cases block with
      | leaf _ => simp [route, frame _ live, read, Bind.bind, Except.bind]
      | branch level children =>
        simp only [route, frame _ live, read, Bind.bind, Except.bind]
        split
        · cases chosen : selectChild key children with
          | none => rfl
          | some child => exact ih (reader_closed valid external live read (List.mem_of_find?_eq_some chosen))
        · rfl

end Silmaril.Proofs.Formats.Dasl.Arena.Prolly.CopyRoot
