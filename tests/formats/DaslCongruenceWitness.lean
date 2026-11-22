module

import Silmaril.Formats.Dasl.Congruence.Witness.Thms

open Silmaril.Formats Silmaril.Formats.Dasl Silmaril.Formats.Dasl.CongruenceWitness
open Silmaril.Semantics Naming

private def frozen : Partial Nat := .ref (.obj 2)

private def witness : Certificate Nat where
  views := ⟨[(1, frozen), (3, frozen)], by decide⟩
  claims := [(1, 3)]

private def readObj (name : Nat) : Option (Shallow Nat) :=
  if name = 1 ∨ name = 3 then some frozen.shallow else none

private def original : Store Nat := ⟨graph readObj, fun _ _ => False⟩
private def readMore (name : Nat) : Option (Shallow Nat) := if name = 2 then some .null else readObj name
private def extended : Store Nat := ⟨graph readMore, fun _ _ => False⟩

private theorem retains : Compatible original extended := by
  refine ⟨⟨?_, fun _ _ hit => hit.elim⟩, graph_binding readMore, fun _ _ _ first => first.elim⟩
  intro name source known
  change readObj name = some source at known
  change readMore name = some source
  by_cases child : name = 2
  · subst name; cases known
  · simpa only [readMore, ite_eq_right child] using known

private theorem view_value {name : Nat} {tree : Partial Nat} (hit : witness.views.lookup? name = some tree) :
    (name = 1 ∨ name = 3) ∧ tree = frozen := by
  rw [OrderedMap.lookup_eq_some_iff] at hit
  change (name, tree) ∈ [(1, frozen), (3, frozen)] at hit
  simpa only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq, ← or_and_right] using hit

private theorem valid : witness.Valid original (fun _ => False) := by
  refine ⟨?_, ?_⟩
  · intro name tree lookup
    obtain ⟨inTable, rfl⟩ := view_value lookup
    exact ⟨⟨ite_eq_left inTable, ⟨fun _ _ hit => hit.elim, fun _ _ hit => hit.elim⟩⟩,
      ⟨fun _ _ hit => hit, fun _ _ hit => hit⟩⟩
  · intro left right known
    change (left, right) ∈ [(1, 3)] at known
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp known)
    exact ⟨rfl, rfl⟩

private theorem checkedEquality : witness.CheckedBy (PER.equality (Partial Nat)) := by
  intro first second edge
  rcases edge with ⟨_, _, equal⟩ | ⟨_, _, _, left, right⟩
  · exact equal
  · exact (view_value left).2.trans (view_value right).2.symm

private theorem equalityClosed : (Tree.constructors (Ref := Link Nat) (Name := Nat) (fun _ => True)).Closed
    (PER.equality (Partial Nat)) := by
  intro shape left right _ _ pointwise
  exact congrArg shape.make (funext pointwise)

example : (witness.named (fun _ => True)).rel 1 3 :=
  Certificate.named_of_edge rfl rfl (.inr ⟨1, 3, by simp [witness], rfl, rfl⟩)

example : ¬ (witness.named (fun _ => True)).Dom 2 := by
  intro supported; have known := (Certificate.named_dom 2).mp supported; cases known

example : witness.Valid extended (fun _ => False) ∧
    witness.named (fun _ => True) ≤ (PER.equality (Partial Nat)).decodePull witness.views.lookup? :=
  Certificate.sound_in_extensions valid (fun _ => PER.equality (Partial Nat))
    (fun _ _ => checkedEquality) (fun _ _ => equalityClosed) extended retains

example : Extends frozen (Named.embed (.obj 2 .null)) :=
  Certificate.Valid.refines_full valid retains (name := 1) rfl ⟨frozen.shallow, rfl, .obj rfl .null⟩
