module

public import Silmaril.Games.Abstract.Module.Defs
public import Silmaril.Games.Abstract.Function.Defs
import Silmaril.Proofs.Games.Abstract.Module.Basic

/-!
# Abstract modules: trap ≈ divergence is a congruence for closing

If two open modules have, function by function, the same call behaviours up
to trap ≈ divergence (`obsCollapse`), then so do their closures, with or
without divergence chains.
-/

public section

namespace Silmaril.Proofs.Games.Abstract.Module

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.Shape Silmaril.Games.Abstract.AFun

universe u

variable {sh : Shape.{u}}

theorem collapse_eq_ret' {S B : Type u} {e : End S B} {b : B} {s : S}
    (h : e.collapse = .ret b s) : e = .ret b s := by
  cases e <;> simp_all [End.collapse]

theorem collapse_eq_abort' {S B : Type u} {e : End S B} (h : e.collapse = .abort) :
    e = .trap ∨ e = .div := by
  cases e <;> simp_all [End.collapse]

/-- Closed modules related up to trap ≈ divergence, one way. -/
def CRel (D D' : sh.ClosedMod) : Prop :=
  ∀ g s a y, y ∈ D g s a → ∃ y' ∈ D' g s a, obsCollapse y = obsCollapse y'

theorem subst_transfer {D D' : sh.ClosedMod} (hD : CRel D D') {R : Type u}
    {cs : List (Call (sh.E ⊕ₛ sh.self))} {e e' : End sh.S R} (he : e.collapse = e'.collapse)
    {y : CallBeh sh.E sh.S R} (h : Subst D cs e y) :
    ∃ y', Subst D' cs e' y' ∧ obsCollapse y = obsCollapse y' := by
  induction h with
  | nil e => exact ⟨([], e'), .nil e', by simp [obsCollapse, he]⟩
  | ext _ ih =>
    obtain ⟨y', hs, hy⟩ := ih he
    refine ⟨(_ :: y'.1, y'.2), .ext hs, ?_⟩
    simp only [obsCollapse, Prod.mk.injEq] at hy ⊢
    exact ⟨by rw [hy.1], hy.2⟩
  | int hc _ ih =>
    obtain ⟨y', hs, hy⟩ := ih he
    obtain ⟨⟨c₂, e₂⟩, hc', hce⟩ := hD _ _ _ _ hc
    simp only [obsCollapse, Prod.mk.injEq] at hce
    obtain ⟨rfl, hce⟩ := hce
    obtain rfl := collapse_eq_ret' hce.symm
    refine ⟨(_ ++ y'.1, y'.2), .int hc' hs, ?_⟩
    simp only [obsCollapse, Prod.mk.injEq] at hy ⊢
    exact ⟨by rw [hy.1], hy.2⟩
  | intTrap hc =>
    obtain ⟨⟨c₂, e₂⟩, hc', hce⟩ := hD _ _ _ _ hc
    simp only [obsCollapse, Prod.mk.injEq] at hce
    obtain ⟨rfl, hce⟩ := hce
    rcases collapse_eq_abort' (by simpa [End.collapse] using hce.symm) with rfl | rfl
    · exact ⟨_, .intTrap hc', rfl⟩
    · exact ⟨_, .intDiv hc', rfl⟩
  | intDiv hc =>
    obtain ⟨⟨c₂, e₂⟩, hc', hce⟩ := hD _ _ _ _ hc
    simp only [obsCollapse, Prod.mk.injEq] at hce
    obtain ⟨rfl, hce⟩ := hce
    rcases collapse_eq_abort' (by simpa [End.collapse] using hce.symm) with rfl | rfl
    · exact ⟨_, .intTrap hc', rfl⟩
    · exact ⟨_, .intDiv hc', rfl⟩

/-- Open modules related up to trap ≈ divergence, one way. -/
def ORel (m m' : sh.OpenMod) : Prop :=
  ∀ f s a x, x ∈ m f s a → ∃ x' ∈ m' f s a, obsCollapse x = obsCollapse x'

theorem close_crel {m m' : sh.OpenMod} (h : ORel m m') : CRel (close m) (close m') := by
  let D : sh.ClosedMod := fun f s a => {y | ∃ y' ∈ close m' f s a, obsCollapse y = obsCollapse y'}
  have hle : close m ≤ D := by
    refine OrderHom.lfp_le _ ?_
    rintro f s a y ⟨x, hx, hs⟩
    obtain ⟨x', hx', hxe⟩ := h f s a x hx
    simp only [obsCollapse, Prod.mk.injEq] at hxe
    have hDc : CRel D (close m') := fun g s a y hy => hy
    obtain ⟨y', hs', hy⟩ := subst_transfer hDc hxe.2 hs
    refine ⟨y', ?_, hy⟩
    rw [← resolve_close m']
    exact ⟨x', hx', hxe.1 ▸ hs'⟩
  exact fun g s a y hy => hle g s a hy

theorem substPre_transfer {D D' : sh.ClosedMod} (hD : CRel D D')
    {u : List (Call (sh.E ⊕ₛ sh.self))} {q : List (Call sh.E)} (h : SubstPre D u q) :
    SubstPre D' u q := by
  induction h with
  | nil => exact .nil
  | ext _ ih => exact .ext ih
  | int hc _ ih =>
    obtain ⟨⟨c₂, e₂⟩, hc', hce⟩ := hD _ _ _ _ hc
    simp only [obsCollapse, Prod.mk.injEq] at hce
    obtain ⟨rfl, hce⟩ := hce
    obtain rfl := collapse_eq_ret' hce.symm
    exact .int hc' ih

theorem divChain_transfer {m m' : sh.OpenMod} (h : ORel m m') {x : sh.self.Op}
    {qs : List (Call sh.E)} (hd : DivChain m (close m) x qs) : DivChain m' (close m') x qs := by
  obtain ⟨g, q, N, h0, hdesc, hq, rfl⟩ := hd
  refine ⟨g, q, N, h0, fun n => ?_, hq, rfl⟩
  obtain ⟨z, hz, u, ans, rest, he, hp⟩ := hdesc n
  obtain ⟨z', hz', hze⟩ := h _ _ _ z hz
  simp only [obsCollapse, Prod.mk.injEq] at hze
  exact ⟨z', hz', u, ans, rest, hze.1 ▸ he, substPre_transfer (close_crel h) hp⟩

theorem closeD_crel {m m' : sh.OpenMod} (h : ORel m m') : CRel (closeD m) (closeD m') := by
  rintro g s a y (hy | ⟨hd, hc⟩)
  · obtain ⟨y', h', e⟩ := close_crel h g s a y hy
    exact ⟨y', .inl h', e⟩
  · exact ⟨y, .inr ⟨hd, divChain_transfer h hc⟩, rfl⟩

theorem orel_of_equiv {m m' : sh.OpenMod} (h : OpenCollapseEquiv m m') : ORel m m' := by
  intro f s a x hx
  obtain ⟨x', hx', he⟩ : obsCollapse x ∈ obsCollapse '' m' f s a := h f s a ▸ ⟨x, hx, rfl⟩
  exact ⟨x', hx', he.symm⟩

theorem equiv_of_crel {c c' : sh.ClosedMod} (h₁ : CRel c c') (h₂ : CRel c' c) :
    ClosedCollapseEquiv c c' := by
  intro f s a
  ext o
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨y', h', e⟩ := h₁ f s a y hy
    exact ⟨y', h', e.symm⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨y', h', e⟩ := h₂ f s a y hy
    exact ⟨y', h', e.symm⟩

theorem close_congr {m m' : sh.OpenMod} (h : OpenCollapseEquiv m m') :
    ClosedCollapseEquiv (close m) (close m') :=
  equiv_of_crel (close_crel (orel_of_equiv h))
    (close_crel (orel_of_equiv fun f s a => (h f s a).symm))

theorem closeD_congr {m m' : sh.OpenMod} (h : OpenCollapseEquiv m m') :
    ClosedCollapseEquiv (closeD m) (closeD m') :=
  equiv_of_crel (closeD_crel (orel_of_equiv h))
    (closeD_crel (orel_of_equiv fun f s a => (h f s a).symm))

end Silmaril.Proofs.Games.Abstract.Module
