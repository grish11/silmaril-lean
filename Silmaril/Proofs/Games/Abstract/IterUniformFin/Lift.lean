module

public import Silmaril.Proofs.Games.Abstract.IterUniformFin.Uniform
public import Silmaril.Games.Abstract.CanonStrat.Thms

/-!
# Uniformity along silent, finitely branching maps for triples and canonical play objects
(proofs)

The full parts are `iter_uniform`. The map has no pending call and is silent, so the pending
calls of `h ; X` are those of `X` at the returns of `h` (`mem_pend_seqT`). Those of
`G ; [inl, inr ∘ h]` are those of `G`. The pending calls of an iteration are those of the body
after a finite continuing chain, and the chains of `F` and `G` correspond (`contChain_lift`,
`contChain_map`). `CanonStrat` follows through the representative triples.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.IterUniformFin

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
  Silmaril.Games.Abstract.StratOps

universe u

variable {E : Sig.{u}} {S A A' B C : Type u}

theorem mem_pend_seqT {h : ObsTriple E S A' A} {X : ObsTriple E S A C} (hh : SilentFinNoTrapT h)
    {s : S} {a : A'} {y : List (Call E) × E.Op} :
    y ∈ (seqT h X).2.1 s a ↔ ∃ x t, ([], End.ret x t) ∈ h.1 s a ∧ y ∈ X.2.1 t x := by
  constructor
  · rintro (hy | ⟨c₁, b, s₁, c₂, m, hc, hm, rfl⟩)
    · rw [hh.1 s a] at hy; exact hy.elim
    · have hc' : c₁ = [] := hh.2.1.2 s a _ hc
      subst hc'
      exact ⟨b, s₁, hc, hm⟩
  · rintro ⟨x, t, hr, hy⟩
    exact .inr ⟨[], x, t, y.1, y.2, hr, hy, rfl⟩

theorem pend_seqT_caseT {h : ObsTriple E S A' A} {G : ObsTriple E S A' (B ⊕ A')}
    (hp : ∀ s a, h.2.1 s a = ∅) (s : S) (a : A') :
    (seqT G (caseT (mapT pureT Sum.inl) (mapT h Sum.inr))).2.1 s a = G.2.1 s a := by
  ext y
  constructor
  · rintro (hy | ⟨c₁, b, s₁, c₂, m, -, hm, -⟩)
    · exact hy
    · cases b with
      | inl b => exact hm.elim
      | inr b =>
        have hm' : (c₂, m) ∈ h.2.1 s₁ b := hm
        rw [hp] at hm'
        exact hm'.elim
  · exact .inl

/-- **Uniformity of iteration for triples** along a silent, trap-free, defined, finitely
branching map with no pending call. -/
theorem iterT_uniform {h : ObsTriple E S A' A} {F : ObsTriple E S A (B ⊕ A)}
    {G : ObsTriple E S A' (B ⊕ A')} (hh : SilentFinNoTrapT h)
    (hFG : seqT h F = seqT G (caseT (mapT pureT Sum.inl) (mapT h Sum.inr))) :
    seqT h (iterT F) = iterT G := by
  have hf : FullFun.seq (full h) (full F) = FullFun.seq (full G) (caseK (full h)) :=
    congrArg full hFG
  have hpend : ∀ s a, (seqT h F).2.1 s a = G.2.1 s a := fun s a => by
    rw [hFG, pend_seqT_caseT hh.1]
  refine ext_full (iter_uniform hh.2 hf) (funext fun s => funext fun a => ?_)
  ext y
  constructor
  · intro hy
    obtain ⟨x, t, hr, c, t', x', c', m, hc, hm, rfl⟩ := (mem_pend_seqT hh).1 hy
    obtain ⟨s', a', hc', hr'⟩ := contChain_lift hh.2 hf hc s a hr
    refine ⟨c, s', a', c', m, hc', ?_, rfl⟩
    rw [← hpend]
    exact (mem_pend_seqT hh).2 ⟨x', t', hr', hm⟩
  · rintro ⟨c, s', a', c', m, hc, hm, rfl⟩
    rw [← hpend] at hm
    obtain ⟨x', t', hr', hm'⟩ := (mem_pend_seqT hh).1 hm
    obtain ⟨x, t, hr, hc'⟩ := contChain_map hh.2 hf hc x' t' hr'
    exact (mem_pend_seqT hh).2 ⟨x, t, hr, c, t', x', c', m, hc', hm', rfl⟩

/-- **Uniformity of iteration for canonical play objects** along a map whose representative is
silent, trap-free, defined, finitely branching and has no pending call. -/
theorem canon_iter_uniform {h : CanonStrat E S A' A} {F : CanonStrat E S A (B ⊕ A)}
    {G : CanonStrat E S A' (B ⊕ A')} (hh : CanonStrat.SilentFinNoTrap h)
    (hFG : CanonStrat.seq h F =
      CanonStrat.seq G (CanonStrat.case (CanonStrat.map CanonStrat.pure Sum.inl)
        (CanonStrat.map h Sum.inr))) :
    CanonStrat.seq h (CanonStrat.iter F) = CanonStrat.iter G := by
  have := congrArg CanonStrat.rep hFG
  simp only [CanonStrat.rep_seq, CanonStrat.rep_case, CanonStrat.rep_map,
    CanonStrat.rep_pure] at this
  exact CanonStrat.rep_injective (by
    simp only [CanonStrat.rep_seq, CanonStrat.rep_iter]
    exact iterT_uniform hh this)

end Silmaril.Proofs.Games.Abstract.IterUniformFin
