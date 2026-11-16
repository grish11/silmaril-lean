module

public import Silmaril.Proofs.Games.Abstract.IterUniform.Uniform
public import Silmaril.Games.Abstract.CanonStrat.Thms

/-!
# Uniformity along silent maps for triples and canonical play objects (proofs)

The full parts are `iter_uniform`. The map has no pending call, so the pending calls of
`h ; X` where `h` returns `(x, t)` are those of `X` at `(t, x)`, and there are none where `h`
diverges. Those of `G ; [inl, inr ∘ h]` are those of `G`. The pending calls of an iteration are
those of the body after a finite continuing chain, and the chains of `F` and `G` correspond
(`contChain_lift`, `contChain_map`). `CanonStrat` follows through the representative triples.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.IterUniform

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
  Silmaril.Games.Abstract.StratOps

universe u

variable {E : Sig.{u}} {S A A' B C : Type u}

theorem pend_seqT_ret {h : ObsTriple E S A' A} {X : ObsTriple E S A C} {s : S} {a : A'}
    {x : A} {t : S} (hp : h.2.1 s a = ∅) (hr : RetAt (full h) s a x t) :
    (seqT h X).2.1 s a = X.2.1 t x := by
  ext y
  constructor
  · rintro (hy | ⟨c₁, b, s₁, c₂, m, hc, hm, rfl⟩)
    · rw [hp] at hy; exact hy.elim
    · have hc' : (c₁, End.ret b s₁) ∈ (full h).1 s a := hc
      rw [hr] at hc'
      obtain ⟨rfl, he⟩ := Prod.mk.inj hc'
      cases he
      exact hm
  · intro hy
    exact .inr ⟨[], x, t, y.1, y.2, (hr ▸ rfl : ([], End.ret x t) ∈ (full h).1 s a), hy, rfl⟩

theorem pend_seqT_div {h : ObsTriple E S A' A} {X : ObsTriple E S A C} {s : S} {a : A'}
    (hp : h.2.1 s a = ∅) (hd : DivAt (full h) s a) : (seqT h X).2.1 s a = ∅ := by
  ext y
  constructor
  · rintro (hy | ⟨c₁, b, s₁, c₂, m, hc, -, -⟩)
    · rw [hp] at hy; exact hy
    · have hc' : (c₁, End.ret b s₁) ∈ (full h).1 s a := hc
      rw [hd] at hc'
      cases (Prod.mk.inj hc').2
  · intro hy; exact hy.elim

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

/-- **Uniformity of iteration for triples** along a silent, deterministic, trap-free, defined
map with no pending call. -/
theorem iterT_uniform {h : ObsTriple E S A' A} {F : ObsTriple E S A (B ⊕ A)}
    {G : ObsTriple E S A' (B ⊕ A')} (hh : SilentDetNoTrapT h)
    (hFG : seqT h F = seqT G (caseT (mapT pureT Sum.inl) (mapT h Sum.inr))) :
    seqT h (iterT F) = iterT G := by
  obtain ⟨hp, hh⟩ := hh
  have hf : FullFun.seq (full h) (full F) = FullFun.seq (full G) (caseK (full h)) :=
    congrArg full hFG
  have hpend : ∀ s a, (seqT h F).2.1 s a = G.2.1 s a := fun s a => by
    rw [hFG, pend_seqT_caseT hp]
  refine ext_full (iter_uniform hh hf) (funext fun s => funext fun a => ?_)
  ext y
  constructor
  · intro hy
    rcases shape hh s a with hd | ⟨x, t, hr⟩
    · rw [pend_seqT_div (hp s a) hd] at hy; exact hy.elim
    · rw [pend_seqT_ret (hp s a) hr] at hy
      obtain ⟨c, t', x', c', m, hc, hm, rfl⟩ := hy
      obtain ⟨s', a', hc', hr'⟩ := contChain_lift hh hf hc s a hr
      refine ⟨c, s', a', c', m, hc', ?_, rfl⟩
      rw [← hpend, pend_seqT_ret (hp s' a') hr']
      exact hm
  · rintro ⟨c, s', a', c', m, hc, hm, rfl⟩
    rcases shape hh s' a' with hd' | ⟨x', t', hr'⟩
    · rw [← hpend, pend_seqT_div (hp s' a') hd'] at hm; exact hm.elim
    · obtain ⟨x, t, hr, hc'⟩ := contChain_map hh hf hc x' t' hr'
      rw [pend_seqT_ret (hp s a) hr]
      refine ⟨c, t', x', c', m, hc', ?_, rfl⟩
      rw [← pend_seqT_ret (X := F) (hp s' a') hr', hpend]
      exact hm

/-- **Uniformity of iteration for canonical play objects** along a map whose representative is
silent, deterministic, trap-free, defined and has no pending call. -/
theorem canon_iter_uniform {h : CanonStrat E S A' A} {F : CanonStrat E S A (B ⊕ A)}
    {G : CanonStrat E S A' (B ⊕ A')} (hh : CanonStrat.SilentDetNoTrap h)
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

end Silmaril.Proofs.Games.Abstract.IterUniform
