module

public import Silmaril.Formats.PER.Fibers.Defs
public import Silmaril.Formats.PER.Thms

public section

namespace Silmaril.Proofs.Formats.PERFibers

open Silmaril.Formats

theorem eq_of_classes {Key : Type} {left right : PER Key} (same : left.classes = right.classes) : left = right := by
  have sub {source target : PER Key} (equal : source.classes = target.classes) : source.Sub target := by
    intro first second related
    have mem : source.classOf first ∈ source.classes := ⟨first, source.dom_left related, rfl⟩
    rw [equal] at mem
    obtain ⟨member, _, group⟩ := mem
    have hfirst : first ∈ target.classOf member := group ▸ source.dom_left related
    have hsecond : second ∈ target.classOf member := group ▸ related
    exact target.laws.trans (target.laws.symm hfirst) hsecond
  exact le_antisymm (sub same) (sub same.symm)

theorem fibers_relabel {Key Label Other : Type} (label : Key → Option Label) (relabel : Label → Other)
    (injective : Function.Injective relabel) : PER.fibers (fun key => (label key).map relabel) = PER.fibers label := by
  apply PER.ext
  intro first second
  constructor
  · rintro ⟨value, hfirst, hsecond⟩
    obtain ⟨beforeFirst, firstHit, rfl⟩ := Option.map_eq_some_iff.mp hfirst
    obtain ⟨beforeSecond, secondHit, equal⟩ := Option.map_eq_some_iff.mp hsecond
    exact ⟨beforeFirst, firstHit, injective equal ▸ secondHit⟩
  · rintro ⟨before, hfirst, hsecond⟩
    exact ⟨relabel before, by simp [hfirst], by simp [hsecond]⟩

end Silmaril.Proofs.Formats.PERFibers
