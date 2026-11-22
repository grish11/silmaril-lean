module

public import Silmaril.Formats.Dasl.PairedShallow.Defs

public section

namespace Silmaril.Proofs.Formats.Dasl

open Silmaril.Formats.Dasl

theorem direct_links_map_iff {Name Next : Type} (names : Name → Next) (tree : Shallow Name) (link : Link Next) :
    link ∈ (Shallow.map names tree).directLinks ↔
      ∃ old, old ∈ tree.directLinks ∧ Link.map names old = link := by
  induction tree with
  | ref old =>
    change link = Link.map names old ↔ ∃ original, original = old ∧ Link.map names original = link
    exact ⟨fun eq => ⟨old, rfl, eq.symm⟩, fun ⟨_, rfl, eq⟩ => eq.symm⟩
  | obj impossible _ _ | blob impossible _ => exact impossible.elim
  | dict keys values ih | list keys values ih =>
    constructor
    · rintro ⟨index, found⟩
      obtain ⟨old, present, eq⟩ := (ih index).mp found
      exact ⟨old, ⟨index, present⟩, eq⟩
    · rintro ⟨old, ⟨index, present⟩, eq⟩
      exact ⟨index, (ih index).mpr ⟨old, present, eq⟩⟩
  | _ => exact ⟨False.elim, fun ⟨_, impossible, _⟩ => impossible.elim⟩

end Silmaril.Proofs.Formats.Dasl
