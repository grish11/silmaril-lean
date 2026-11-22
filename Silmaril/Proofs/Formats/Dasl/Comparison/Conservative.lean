module

public import Silmaril.Formats.Dasl.Named.Thms
public import Silmaril.Formats.Dasl.Resolve.View.Thms

public section

namespace Silmaril.Proofs.Formats.Dasl

open Silmaril.Formats.Dasl

theorem fullLookup_eq_some_iff_observe {Name : Type} (reader : Reader Name) {root : Name} {tree : Named Name} :
    fullLookup reader.binding root = some tree ↔
      ∃ fuel, reader.observeRoot? fuel root = some tree.embed := by
  rw [fullLookup_eq_some]
  constructor
  · intro full
    obtain ⟨fuel, ready⟩ := reader.observeRoot_eventually full
    exact ⟨fuel, ready fuel le_rfl⟩
  · rintro ⟨fuel, observed⟩
    obtain ⟨hit, admitted⟩ := reader.observeRoot_sound observed
    exact ⟨_, hit, Named.admitted_iff_expands.mp admitted⟩

end Silmaril.Proofs.Formats.Dasl
