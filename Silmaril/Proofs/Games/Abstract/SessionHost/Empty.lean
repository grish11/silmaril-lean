module

public import Silmaril.Games.Abstract.SessionHost.Defs

/-!
# Host imports only (proofs)

With no component imports (`F = Sig.empty`) the host on `F` is `StratHost.hostD R`, and the linked
triple is the closed triple `StratHost.linkT` of the function-level model: every log of
`Sig.empty` is empty, so there is no pending call and no productive stream, and the chatter of a
stream with only host calls is the divergence after an allowed productive stream.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.SessionHost

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.SessionHost
  Silmaril.Games.Abstract.StratObs Silmaril.Games.Abstract.StratHost

universe u

variable {E : Sig.{u}} {S A B : Type u} {R : HostRel E}

theorem calls_empty (l : List (Call Sig.empty.{u})) : l = [] := by
  rcases l with _ | ⟨⟨m, _⟩, _⟩
  · rfl
  · exact m.elim

theorem hostOnS_empty : hostOnS Sig.empty.{u} R = hostS R := by
  refine Strategy.ext fun s => and_congr_right fun _ => ⟨fun h m n hm => h _ hm, fun h o ho => ?_⟩
  rcases o with (⟨m⟩ | ⟨m, _⟩) | (_ | ⟨m, n⟩)
  · exact m.elim
  · exact m.elim
  · trivial
  · exact h m n ho

/-- **The host on the empty interface is the host.** -/
theorem hostDOn_empty : hostDOn Sig.empty.{u} R = hostD R :=
  DStrategy.ext hostOnS_empty
    (Set.ext fun s => by
      show (s ∈ hostOnS _ R ∧ _) ↔ (s ∈ hostS R ∧ _)
      rw [hostOnS_empty])
    (Set.ext fun I => by
      show (_ ∧ I ⊆ (hostOnS _ R).plays) ↔ (_ ∧ I ⊆ (hostS R).plays)
      rw [hostOnS_empty])

/-- **With host imports only, the linked triple is `linkT`.** -/
theorem hostLinkS_empty (t : ObsTriple (E ⊕ₛ Sig.empty.{u}) S A B) :
    hostLinkS R t = linkT (sumL R Sig.empty) t := by
  refine Prod.ext (funext fun s => funext fun a => Set.ext fun x => ?_)
    (Prod.ext (funext fun s => funext fun a => Set.ext fun x => x.2.elim)
      (funext fun s => funext fun a => Set.ext fun ω => (ω 0).1.elim))
  have hx : ∀ c : List (Call (E ⊕ₛ Sig.empty.{u})), x.1 = fCalls c := fun c =>
    (calls_empty _).trans (calls_empty _).symm
  constructor
  · rintro (⟨c, hc, hok, -⟩ | ⟨hd, ⟨c, m, hP, hok, hdv, -⟩ | ⟨ω, hω, -⟩⟩)
    · exact .inl ⟨c, hc, hok⟩
    · exact .inr ⟨hd, .inl ⟨c, .inl m, ⟨hP, hok, .inr hdv⟩, hdv⟩⟩
    · exact .inr ⟨hd, .inr ⟨ω, hω⟩⟩
  · rintro (⟨c, hc, hok⟩ | ⟨hd, ⟨c, μ, ⟨hP, hok, -⟩, hdv⟩ | ⟨ω, hω⟩⟩)
    · exact .inl ⟨c, hc, hok, hx c⟩
    · rcases μ with m | m
      · exact .inr ⟨hd, .inl ⟨c, m, hP, hok, hdv, hx c⟩⟩
      · exact m.elim
    · exact .inr ⟨hd, .inr ⟨ω, hω, 0, fun k _ => calls_empty _, hx _⟩⟩

end Silmaril.Proofs.Games.Abstract.SessionHost
