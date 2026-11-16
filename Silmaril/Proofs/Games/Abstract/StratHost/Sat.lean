module

public import Silmaril.Games.Abstract.StratHost.Defs
public import Silmaril.Games.Abstract.StratObs.Thms

/-!
# Restriction and linking of saturated triples (proofs)

* `saturated_guardT`: restricting the questions keeps a triple saturated (every component of
  `guardT Ok t` is guarded by the same question);
* `linkT_hostRestrict`: on a saturated triple, linking after the host restriction is linking.
  The two links differ only in the host-divergence clause, where `linkT` takes the call prefixes
  of the saturation: those of `hostRestrict R t` are call prefixes of `t`, and conversely a call
  prefix of a saturated `t` is a pending call, kept by the restriction when its log is allowed
  and `R` may diverge there.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.StratHost

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratHost

universe u

variable {E : Sig.{u}} {S A B : Type u}

theorem saturated_guardT {Ok : S → A → Prop} {t : ObsTriple E S A B}
    (ht : StratObs.Saturated t) : StratObs.Saturated (guardT Ok t) := by
  rw [StratObs.saturated_iff] at ht ⊢
  funext s a
  ext x
  refine ⟨?_, fun h => .inl h⟩
  rintro (h | ⟨d, m', ⟨hok, hd⟩, hc⟩ | ⟨d, e, ⟨hok, hd⟩, hc⟩ | ⟨ω, ⟨hok, hω⟩, k, h₁, h₂⟩)
  · exact h
  · exact ⟨hok, ht ▸ .inr (.inl ⟨d, m', hd, hc⟩)⟩
  · exact ⟨hok, ht ▸ .inr (.inr (.inl ⟨d, e, hd, hc⟩))⟩
  · exact ⟨hok, ht ▸ .inr (.inr (.inr ⟨ω, hω, k, h₁, h₂⟩))⟩

theorem linkT_hostRestrict (R : HostRel E) {t : ObsTriple E S A B}
    (ht : StratObs.Saturated t) : linkT R (hostRestrict R t) = linkT R t := by
  rw [StratObs.saturated_iff] at ht
  refine Prod.ext (funext fun s => funext fun a => Set.ext fun x => ?_) rfl
  constructor
  · rintro (⟨c, h⟩ | ⟨hd, ⟨c, m, ⟨h, hc, hs⟩, hm⟩ | ⟨ω, hω⟩⟩)
    · exact .inl ⟨c, h.1⟩
    · refine .inr ⟨hd, .inl ⟨c, m, ⟨?_, hc, hs⟩, hm⟩⟩
      rcases h with h | ⟨d, m', hd', hc'⟩ | ⟨d, e, hd', hc'⟩ | ⟨ω, hω, k, h₁, h₂⟩
      · exact .inl h.1
      · exact .inr (.inl ⟨d, m', hd'.1, hc'⟩)
      · exact .inr (.inr (.inl ⟨d, e, hd'.1, hc'⟩))
      · exact .inr (.inr (.inr ⟨ω, hω.1, k, h₁, h₂⟩))
    · exact .inr ⟨hd, .inr ⟨ω, hω.1⟩⟩
  · rintro (⟨c, h⟩ | ⟨hd, ⟨c, m, ⟨h, hc, hs⟩, hm⟩ | ⟨ω, hω⟩⟩)
    · exact .inl ⟨c, h, h.2⟩
    · have hp : (c, m) ∈ t.2.1 s a := ht ▸ h
      exact .inr ⟨hd, .inl ⟨c, m, ⟨.inl ⟨hp, hc, .inr hm⟩, hc, hs⟩, hm⟩⟩
    · exact .inr ⟨hd, .inr ⟨ω, hω, hω.2⟩⟩

end Silmaril.Proofs.Games.Abstract.StratHost
