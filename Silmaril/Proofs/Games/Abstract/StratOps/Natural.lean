module

public import Silmaril.Proofs.Games.Abstract.StratOps.Laws
import Silmaril.Games.Abstract.FullFun.Thms

/-!
# Naturality and uniformity of iteration for triples (proofs)

The full parts are `FullFun.iter_map` and `FullFun.iter_uniform_comap`. The pending calls of an
iteration are those of the body after a finite continuing chain. Mapping the exit value keeps
the chains (`FullFun.contChain_map`). Under the uniformity hypothesis, chains of the two bodies
correspond (`FullFun.contChain_uniform`, `FullFun.contChain_lift`), and the pending calls of `F`
at `k a` are those of `G` at `a`.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.StratOps

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
  Silmaril.Games.Abstract.StratOps

universe u

variable {E : Sig.{u}} {S A A' B C : Type u}

/-- **Naturality of iteration in the output** for triples. -/
theorem iterT_mapT (t : ObsTriple E S A (B ⊕ A)) (h : B → C) :
    iterT (mapT t (Sum.map h id)) = mapT (iterT t) h := by
  refine ext_full (FullFun.iter_map (full t) h) (funext fun s => funext fun a => ?_)
  ext x
  constructor
  · rintro ⟨c, s', a', c', m, hc, hp, rfl⟩
    exact ⟨c, s', a', c', m, (FullFun.contChain_map (full t) h).1 hc, hp, rfl⟩
  · rintro ⟨c, s', a', c', m, hc, hp, rfl⟩
    exact ⟨c, s', a', c', m, (FullFun.contChain_map (full t) h).2 hc, hp, rfl⟩

/-- The copairing of pure maps is a pure map. -/
theorem caseT_pureT_mapT_mapT {X : Type u} (h₁ : A → X) (h₂ : B → X) :
    caseT (mapT (pureT : ObsTriple E S A A) h₁) (mapT pureT h₂) = mapT pureT (Sum.elim h₁ h₂) :=
  ext_full (FullFun.case_pure_map_map h₁ h₂) (funext fun _ => funext fun x => by cases x <;> rfl)

/-- **Uniformity of iteration** for triples, pre-composition form. -/
theorem iterT_uniform_comap {F : ObsTriple E S A (B ⊕ A)} {G : ObsTriple E S A' (B ⊕ A')}
    {k : A' → A} (hFG : comapT F k = mapT G (Sum.map id k)) : comapT (iterT F) k = iterT G := by
  have hf : (full F).comap k = (full G).map (Sum.map id k) := congrArg full hFG
  have hp : ∀ s a, F.2.1 s (k a) = G.2.1 s a := fun s a =>
    congrFun (congrFun (congrArg (fun t => t.2.1) hFG) s) a
  refine ext_full (FullFun.iter_uniform_comap hf) (funext fun s => funext fun a => ?_)
  ext x
  constructor
  · rintro ⟨c, s', x', c', m, hc, hpm, rfl⟩
    obtain ⟨a', rfl, hc'⟩ := FullFun.contChain_lift hf hc
    exact ⟨c, s', a', c', m, hc', (hp s' a') ▸ hpm, rfl⟩
  · rintro ⟨c, s', a', c', m, hc, hpm, rfl⟩
    exact ⟨c, s', k a', c', m, FullFun.contChain_uniform hf hc, (hp s' a').symm ▸ hpm, rfl⟩

/-- **Uniformity of iteration** for triples (Elgot form), for a pure map `h`. -/
theorem iterT_uniform {F : ObsTriple E S A (B ⊕ A)} {G : ObsTriple E S A' (B ⊕ A')}
    (h : A' → A)
    (hFG : seqT (mapT pureT h) F =
      seqT G (caseT (mapT pureT Sum.inl) (mapT pureT (Sum.inr ∘ h)))) :
    seqT (mapT pureT h) (iterT F) = iterT G := by
  rw [caseT_pureT_mapT_mapT, seqT_pureT_mapT, pureT_mapT_seqT] at hFG
  rw [pureT_mapT_seqT]
  exact iterT_uniform_comap (hFG.trans (congrArg (mapT G) (funext fun x => by cases x <;> rfl)))

end Silmaril.Proofs.Games.Abstract.StratOps
