module

import Silmaril.Formats.Dasl.Resolve.Refinement.Thms
import Silmaril.Formats.Dasl.Resolve.View.Thms

open Silmaril.Formats.Dasl

private def source : Shallow Bool := .list 1 fun _ => .ref (.obj true)
private def reader : Reader Bool := ⟨fun name => some (if name then .null else source), fun _ => none⟩
private def complete : Named Bool := .list 1 fun _ => .obj true .null

private theorem rootFull : FullNames reader.store false complete :=
  ⟨source, rfl, .list fun _ => .obj rfl .null⟩

example : Extends source.embed complete.embed := by
  apply rootFull.refines reader.binding
  exact reader.observeRoot_sound (fuel := 0) (root := false) rfl

example : ∃ observed, PartialNames reader.store false observed ∧ observed.HasKnownBinding :=
  (nontrivial_partial_iff reader.binding false).mpr
    ⟨source, rfl, .inl ⟨true, .null, ⟨⟨0, by decide⟩, rfl⟩, rfl⟩⟩
