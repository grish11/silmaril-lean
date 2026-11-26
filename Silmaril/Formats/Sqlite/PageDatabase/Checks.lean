module

import Silmaril.Formats.Sqlite.PageDatabase.Thms
import Mathlib.Data.Nat.Basic

namespace Silmaril.Formats.Sqlite.PageDatabase

open Silmaril.Semantics

-- Each table decodes an addressed payload as a typed row on its own leaf.
private def leafTable (address key value : Nat) : Table Nat Unit (fun _ => Nat) Nat :=
  { schema := ⟨1, fun _ => ()⟩
    tree := ⟨0, [(key, fun _ => value)]⟩
    layout := fun _ => address
    decode := fun page data => if page = address then some (.leaf [(key, fun _ => data)]) else none }

private def pages : Page.UndefArray 3 Nat
  | ⟨0, _⟩ => some 5
  | ⟨2, _⟩ => some 6
  | _ => none

private def left := leafTable 0 7 5
private def right := leafTable 2 8 6
private def db : Database Nat Unit (fun _ => Nat) Nat := ⟨[("left", left), ("right", right)]⟩

private theorem leaf_rep {p key value : Nat} (h : p < 3) (cell : pages ⟨p, h⟩ = some value) :
    (leafTable p key value).Represents pages := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp [leafTable, BTree.Tree.Valid, BTree.Node.ValidWithin, BTree.InRange]
  · intro l r hl hr _
    cases l <;> cases r <;> first | rfl | exact (hl rfl).elim | exact (hr rfl).elim
  · intro path data atPage
    cases path with
    | nil =>
      cases atPage
      simp [leafTable, Table.decodedMemory, Page.mapStore, Page.UndefArray.toMemory, BTreePages.encode, h, cell]
    | cons => cases atPage

private theorem db_rep : db.Represents pages := by
  refine ⟨by decide, ?_, ?_⟩
  · simp [db, List.pairwise_cons]
    intro p leftPage rightPage
    obtain ⟨l, _, leftAddr⟩ := leftPage
    obtain ⟨r, _, rightAddr⟩ := rightPage
    have same : (0 : Nat) = 2 := leftAddr.trans rightAddr.symm
    exact (by decide : (0 : Nat) ≠ 2) same
  · simpa [db] using
      ⟨leaf_rep (p := 0) (key := 7) (value := 5) (by decide) rfl,
        leaf_rep (p := 2) (key := 8) (value := 6) (by decide) rfl⟩

example : db.find? "right" = some right := rfl
example : left.rows.map (fun row => row ⟨0, by decide⟩) = [5] := rfl
example : (right.readModel.get 8).map (fun row => row ⟨0, by decide⟩) = some 6 := rfl

example : db.Validates db 3 [.write 1 9, .read 1 9] := by
  let final := Page.override pages (1 : Fin 3) (some 9)
  have run : ReadWrite.Trace.Replays (Page.UndefArray.access 3 Nat)
      [.write 1 9, .read 1 9] pages final := ReadWrite.Trace.run_eq_some_iff.mp rfl
  refine ⟨pages, final, db_rep, run, Database.replays_frame db_rep run ?_⟩
  rintro p ⟨entry, member, pos, _, eq⟩ ⟨value, written⟩
  have atWrite : p = 1 := (Prod.mk.inj (List.mem_singleton.mp written)).1
  rw [atWrite] at eq
  rcases List.mem_cons.mp member with equality | member
  · subst entry
    exact (by decide : (0 : Nat) ≠ 1) eq
  · have equality := List.mem_singleton.mp member
    subst entry
    exact (by decide : (2 : Nat) ≠ 1) eq

end Silmaril.Formats.Sqlite.PageDatabase
