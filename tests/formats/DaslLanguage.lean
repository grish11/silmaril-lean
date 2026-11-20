module

import Silmaril.Formats.Dasl.Language.Check.Wire.Thms
meta import Silmaril.Formats.Dasl.Language.Check.Wire.Defs

open Silmaril.Formats.Dasl Silmaril.Semantics.Naming

private def roots : PartialLanguage Bool := fun name tree => name = false ∧ tree = .ref (.blob true)

private def external : Store Bool := ⟨fun _ _ => False, graph fun _ => some ByteArray.empty⟩

private def reference : Store Bool :=
  ⟨graph (fun name => if name then none else some (.ref (.blob true))), external.blobs⟩

private theorem compatible : roots.observed.MergeCompatible external := by
  apply Stores.mergeCompatible_iff.mpr
  refine ⟨reference, PartialLanguage.observed_subset_iff.mpr ?_, ⟨?_, fun _ _ hit => hit⟩,
    ⟨graph_binding _, graph_binding _⟩⟩
  · rintro root tree ⟨rfl, rfl⟩
    exact PartialNames.shallow (source := .ref (.blob true)) rfl
  · intro _ _ hit
    exact hit.elim

example : roots.expand external compatible false (.blob true ByteArray.empty) := by
  refine ⟨.ref (.blob true), ⟨rfl, rfl⟩, .openBlob true ByteArray.empty, ?_⟩
  refine ⟨Or.inl (PartialLanguage.satisfies_observed roots ⟨rfl, rfl⟩).1, ⟨?_, ?_⟩⟩
  · intro _ _ hit
    exact hit.elim
  · rintro _ _ ⟨rfl, rfl⟩
    exact Or.inr rfl

example : ¬ (roots.expand external compatible).Satisfies external := by
  intro satisfies
  have included := PartialLanguage.expand_satisfies_external_iff.mp satisfies
  exact ((PartialLanguage.observed_subset_iff.mp included) (root := false) (tree := .ref (.blob true)) ⟨rfl, rfl⟩).1

example : ¬ roots.expand external compatible false (.blob true ⟨#[0xFF]⟩) := by
  rintro ⟨_, _, _, _, _, blobs⟩
  rcases blobs (name := true) (payload := ⟨#[0xFF]⟩) ⟨rfl, rfl⟩ with old | supplied
  · obtain ⟨_, _, ⟨_, rfl⟩, noBlob⟩ := old
    exact noBlob
  · cases supplied

example : ¬ external.Subset (PartialLanguage.realize (fun _ _ => False) external).observed := by
  intro included
  have hit := included.2 (name := false) (payload := ByteArray.empty) rfl
  obtain ⟨_, _, ⟨noRoot, _⟩, _⟩ := hit
  exact noRoot

private def cidTag (codec digest : UInt8) : List UInt8 :=
  [0xD8, 0x2A, 0x58, 37, 0, 1, codec, 0x12, 32] ++ List.replicate 32 digest

private def expect (condition : Bool) (label : String) : IO Unit :=
  unless condition do throw (IO.userError label)

public def main : IO Unit := do
  let some (.ref (.obj root)) := Wire.parse? (cidTag 0x71 0).toByteArray | throw (IO.userError "root CID")
  let some (.ref (.obj child)) := Wire.parse? (cidTag 0x71 1).toByteArray | throw (IO.userError "child CID")
  let some (.ref (.blob raw)) := Wire.parse? (cidTag 0x55 0).toByteArray | throw (IO.userError "raw CID")
  let rootBytes := ([0xA2, 0x61, 0x61, 0x81] ++ cidTag 0x71 1 ++ [0x61, 0x62] ++ cidTag 0x55 0).toByteArray
  let read (childBytes : Option ByteArray) (blobBytes : Option ByteArray) (key : Wire.Cid) :=
    if key.val == root.val then some rootBytes else if key.val == child.val then childBytes
    else if key.val == raw.val then blobBytes else none
  let queries (fetch : Wire.Cid → Option ByteArray) := Wire.queries fetch (Stores.Subset.refl (Wire.queryStore fetch))
  let accepts : Value → Bool := fun tree => match tree with | .dict _ _ => true | _ => false
  let childBytes := some (⟨#[0xF5]⟩ : ByteArray)
  let blobBytes := some ByteArray.empty
  let complete := queries (read childBytes blobBytes)
  expect (decide (Check.run complete accepts 1 root = .accepted)) "resolve dict/list children before accepting"
  expect (decide (Check.run complete (fun _ => false) 1 root = .rejected)) "fully resolved rejection"
  expect (decide (Check.run complete accepts 0 root = .undecided (.fuel (.obj child)))) "exhausted link budget"
  expect (decide (Check.run (queries (fun _ => none)) accepts 1 root = .undecided (.missing (.obj root)))) "missing root"
  expect (decide (Check.run (queries (read none blobBytes)) accepts 1 root = .undecided (.missing (.obj child)))) "missing child"
  expect (decide (Check.run (queries (read (some ⟨#[0xFF]⟩) blobBytes)) accepts 1 root = .undecided (.invalid (.obj child)))) "invalid wire child"
  expect (decide (Check.run (queries (read childBytes none)) accepts 1 root = .undecided (.missing (.blob raw)))) "missing blob"
  expect (decide (Check.run complete accepts 1 raw = .undecided (.invalid (.obj raw)))) "invalid root codec"
