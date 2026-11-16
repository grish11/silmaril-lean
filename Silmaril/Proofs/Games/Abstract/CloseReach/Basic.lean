module

public import Silmaril.Games.Abstract.CloseReach.Defs

/-!
# Closing with reach (proofs)

Splitting a resolution of `u ++ v` at the end of `u` (`subst_append`), resolving a
returned prefix in front of a resolution (`subst_append_of_substPre`), the order
facts of `closeR`, and the agreement of `closeR` with the closure of the cut
module.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.CloseReach

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.Shape

universe u

variable {sh : Shape.{u}}

/-! ## Resolutions of an appended behaviour -/

/-- A resolution that ends early inside `u`: at an internal call of `u` after the
returned prefix `u₁`, the callee traps or diverges. -/
def EarlyEnd (c : sh.ClosedMod) (u : List (Call (sh.E ⊕ₛ sh.self))) {R : Type u}
    (w : CallBeh sh.E sh.S R) : Prop :=
  ∃ u₁ z ans u₂ q c₁, u = u₁ ++ ⟨.inr z, ans⟩ :: u₂ ∧ SubstPre c u₁ q ∧
    (((c₁, .trap) ∈ c z.1 z.2.2 z.2.1 ∧ w = (q ++ c₁, .trap)) ∨
      ((c₁, .div) ∈ c z.1 z.2.2 z.2.1 ∧ w = (q ++ c₁, .div)))

theorem subst_append {c : sh.ClosedMod} {R : Type u} {e : End sh.S R}
    (u v : List (Call (sh.E ⊕ₛ sh.self))) {w : CallBeh sh.E sh.S R}
    (h : Subst c (u ++ v) e w) :
    EarlyEnd c u w ∨ ∃ q w', SubstPre c u q ∧ Subst c v e w' ∧ w = (q ++ w'.1, w'.2) := by
  induction u generalizing w with
  | nil => exact .inr ⟨[], w, .nil, h, rfl⟩
  | cons x u ih =>
    obtain ⟨op, ans⟩ := x
    rw [List.cons_append] at h
    cases h with
    | @ext m n _ _ y h' =>
      rcases ih h' with ⟨u₁, z, ans', u₂, q, c₁, rfl, hq, hz⟩ | ⟨q, w', hq, hv, rfl⟩
      · refine .inl ⟨⟨.inl m, n⟩ :: u₁, z, ans', u₂, ⟨m, n⟩ :: q, c₁, rfl, .ext hq, ?_⟩
        rcases hz with ⟨hm, rfl⟩ | ⟨hm, rfl⟩
        exacts [.inl ⟨hm, rfl⟩, .inr ⟨hm, rfl⟩]
      · exact .inr ⟨⟨m, n⟩ :: q, w', .ext hq, hv, rfl⟩
    | @int g a s b s' _ _ c₀ y hc h' =>
      rcases ih h' with ⟨u₁, z, ans', u₂, q, c₁, rfl, hq, hz⟩ | ⟨q, w', hq, hv, rfl⟩
      · refine .inl ⟨_ :: u₁, z, ans', u₂, c₀ ++ q, c₁, rfl, .int hc hq, ?_⟩
        rcases hz with ⟨hm, rfl⟩ | ⟨hm, rfl⟩
        exacts [.inl ⟨hm, by simp⟩, .inr ⟨hm, by simp⟩]
      · exact .inr ⟨c₀ ++ q, w', .int hc hq, hv, by simp⟩
    | intTrap hc => exact .inl ⟨[], _, _, _, [], _, rfl, .nil, .inl ⟨hc, rfl⟩⟩
    | intDiv hc => exact .inl ⟨[], _, _, _, [], _, rfl, .nil, .inr ⟨hc, rfl⟩⟩

theorem subst_append_of_substPre {c : sh.ClosedMod} {R : Type u} {e : End sh.S R}
    {u v : List (Call (sh.E ⊕ₛ sh.self))} {q : List (Call sh.E)} {w : CallBeh sh.E sh.S R}
    (hq : SubstPre c u q) (hv : Subst c v e w) : Subst c (u ++ v) e (q ++ w.1, w.2) := by
  induction hq with
  | nil => exact hv
  | ext _ ih => exact .ext ih
  | int hc _ ih => rw [List.append_assoc]; exact .int hc ih

theorem subst_trap {c : sh.ClosedMod} {R : Type u} {e : End sh.S R}
    {u rest : List (Call (sh.E ⊕ₛ sh.self))} {q c₁ : List (Call sh.E)} {z : sh.self.Op}
    {ans : sh.self.Ar z} (hq : SubstPre c u q) (hz : (c₁, .trap) ∈ c z.1 z.2.2 z.2.1) :
    Subst c (u ++ ⟨.inr z, ans⟩ :: rest) e (q ++ c₁, .trap) := by
  obtain ⟨g, a, s⟩ := z
  exact subst_append_of_substPre hq (.intTrap hz)

theorem subst_div {c : sh.ClosedMod} {R : Type u} {e : End sh.S R}
    {u rest : List (Call (sh.E ⊕ₛ sh.self))} {q c₁ : List (Call sh.E)} {z : sh.self.Op}
    {ans : sh.self.Ar z} (hq : SubstPre c u q) (hz : (c₁, .div) ∈ c z.1 z.2.2 z.2.1) :
    Subst c (u ++ ⟨.inr z, ans⟩ :: rest) e (q ++ c₁, .div) := by
  obtain ⟨g, a, s⟩ := z
  exact subst_append_of_substPre hq (.intDiv hz)

/-! ## Order facts -/

theorem resolve_le_resolveR (m : sh.OpenMod) (Rch : sh.ReachRel) (c : sh.ClosedMod) :
    resolve m c ≤ resolveR m Rch c :=
  fun _ _ _ _ hy => .inl hy

theorem close_le_closeR (m : sh.OpenMod) (Rch : sh.ReachRel) : close m ≤ closeR m Rch :=
  OrderHom.lfp_le _ ((resolve_le_resolveR m Rch _).trans (le_of_eq (OrderHom.map_lfp _)))

theorem resolveR_closeR (m : sh.OpenMod) (Rch : sh.ReachRel) :
    resolveR m Rch (closeR m Rch) = closeR m Rch :=
  OrderHom.map_lfp _

theorem resolveR_mono {m m' : sh.OpenMod} {Rch Rch' : sh.ReachRel} (hm : m ≤ m')
    (hr : Rch ≤ Rch') : resolveR m Rch ≤ resolveR m' Rch' := by
  intro c f s a y hy
  rcases hy with ⟨x, hx, hs⟩ | ⟨u, q, z, c₁, hrz, hq, hz⟩
  · exact .inl ⟨x, hm _ _ _ hx, hs⟩
  · exact .inr ⟨u, q, z, c₁, hr _ _ _ hrz, hq, hz⟩

theorem closeR_mono {m m' : sh.OpenMod} {Rch Rch' : sh.ReachRel} (hm : m ≤ m')
    (hr : Rch ≤ Rch') : closeR m Rch ≤ closeR m' Rch' :=
  OrderHom.lfp.monotone (resolveR_mono hm hr)

/-- Reach that `m` already makes (the reached call is in a behaviour of `m`
after the same prefix) adds nothing. -/
theorem resolveR_le_resolve {m : sh.OpenMod} {Rch : sh.ReachRel}
    (hsyn : ∀ x u y, Rch x u y →
      ∃ w ∈ m x.1 x.2.2 x.2.1, ∃ ans rest, w.1 = u ++ ⟨.inr y, ans⟩ :: rest)
    (c : sh.ClosedMod) : resolveR m Rch c ≤ resolve m c := by
  intro f s a y hy
  rcases hy with hy | ⟨u, q, z, c₁, hrz, hq, hz⟩
  · exact hy
  · obtain ⟨w, hw, ans, rest, he⟩ := hsyn _ _ _ hrz
    refine ⟨w, hw, ?_⟩
    rw [he]
    rcases hz with ⟨hm, rfl⟩ | ⟨hm, rfl⟩
    exacts [subst_trap hq hm, subst_div hq hm]

theorem closeR_eq_close {m : sh.OpenMod} {Rch : sh.ReachRel}
    (hsyn : ∀ x u y, Rch x u y →
      ∃ w ∈ m x.1 x.2.2 x.2.1, ∃ ans rest, w.1 = u ++ ⟨.inr y, ans⟩ :: rest) :
    closeR m Rch = close m :=
  le_antisymm
    (OrderHom.lfp_le _ ((resolveR_le_resolve hsyn _).trans (le_of_eq (OrderHom.map_lfp _))))
    (close_le_closeR m Rch)

theorem closeR_bot (m : sh.OpenMod) : closeR m ⊥ = close m :=
  closeR_eq_close fun _ _ _ h => (h : False).elim

/-! ## Cut behaviours -/

/-- Resolving the cut module against `d` stays within reach resolution, when
reach prefixes are closed and `d` returns no `Bad` answer. -/
theorem resolve_cutMod_le {m : sh.OpenMod} {Rch : sh.ReachRel}
    {Bad : (y : sh.self.Op) → sh.self.Ar y → Prop} {d : sh.ClosedMod}
    (hpc : ReachPrefixClosed m Rch)
    (hbad : ∀ (y : sh.self.Op) c₁ b s', (c₁, .ret b s') ∈ d y.1 y.2.2 y.2.1 → ¬ Bad y (b, s')) :
    resolve (cutMod m Rch Bad) d ≤ resolveR m Rch d := by
  intro f s a w ⟨x, hx, hs⟩
  rcases hx with hx | ⟨u, y, ans, hr, hb, rfl⟩
  · exact .inl ⟨x, hx, hs⟩
  rcases subst_append u _ hs with ⟨u₁, z, ans', u₂, q, c₁, rfl, hq, hz⟩ | ⟨q, w', hq, hv, rfl⟩
  · rcases hpc _ _ _ hr u₁ z ans' u₂ rfl with hr' | ⟨w₀, hw₀, ans'', rest, he⟩
    · exact .inr ⟨u₁, q, z, c₁, hr', hq, hz⟩
    · refine .inl ⟨w₀, hw₀, ?_⟩
      rw [he]
      rcases hz with ⟨hm, rfl⟩ | ⟨hm, rfl⟩
      exacts [subst_trap hq hm, subst_div hq hm]
  · obtain ⟨g, a', s'⟩ := y
    cases hv with
    | int hc hn => exact absurd hb (hbad ⟨g, (a', s')⟩ _ _ _ hc)
    | intTrap hc => exact .inr ⟨u, q, _, _, hr, hq, .inl ⟨hc, rfl⟩⟩
    | intDiv hc => exact .inr ⟨u, q, _, _, hr, hq, .inr ⟨hc, rfl⟩⟩

/-- Reach resolution stays within resolving the cut module, when every reached
call has a `Bad` answer. -/
theorem resolveR_le_resolve_cutMod {m : sh.OpenMod} {Rch : sh.ReachRel}
    {Bad : (y : sh.self.Op) → sh.self.Ar y → Prop}
    (hne : ∀ x u y, Rch x u y → ∃ ans, Bad y ans) (d : sh.ClosedMod) :
    resolveR m Rch d ≤ resolve (cutMod m Rch Bad) d := by
  intro f s a w hw
  rcases hw with ⟨x, hx, hs⟩ | ⟨u, q, z, c₁, hr, hq, hz⟩
  · exact ⟨x, .inl hx, hs⟩
  obtain ⟨ans, hb⟩ := hne _ _ _ hr
  refine ⟨(u ++ [⟨.inr z, ans⟩], .trap), .inr ⟨u, z, ans, hr, hb, rfl⟩, ?_⟩
  rcases hz with ⟨hm, rfl⟩ | ⟨hm, rfl⟩
  exacts [subst_trap hq hm, subst_div hq hm]

theorem closeR_le_close_cutMod {m : sh.OpenMod} {Rch : sh.ReachRel}
    {Bad : (y : sh.self.Op) → sh.self.Ar y → Prop}
    (hne : ∀ x u y, Rch x u y → ∃ ans, Bad y ans) :
    closeR m Rch ≤ close (cutMod m Rch Bad) :=
  OrderHom.lfp_le _ ((resolveR_le_resolve_cutMod hne _).trans (le_of_eq (OrderHom.map_lfp _)))

theorem close_cutMod_le_closeR {m : sh.OpenMod} {Rch : sh.ReachRel}
    {Bad : (y : sh.self.Op) → sh.self.Ar y → Prop} (hpc : ReachPrefixClosed m Rch)
    (hbad : ∀ (y : sh.self.Op) c₁ b s',
      (c₁, .ret b s') ∈ close (cutMod m Rch Bad) y.1 y.2.2 y.2.1 → ¬ Bad y (b, s')) :
    close (cutMod m Rch Bad) ≤ closeR m Rch := by
  have hd : resolve (cutMod m Rch Bad) (closeR m Rch ⊓ close (cutMod m Rch Bad)) ≤
      closeR m Rch ⊓ close (cutMod m Rch Bad) :=
    le_inf
      ((resolve_cutMod_le hpc fun y c₁ b s' hc => hbad y c₁ b s' (inf_le_right (a := closeR m Rch)
          _ _ _ hc)).trans
        (((resolveR m Rch).monotone inf_le_left).trans (le_of_eq (OrderHom.map_lfp _))))
      (((resolve _).monotone inf_le_right).trans (le_of_eq (OrderHom.map_lfp _)))
  exact (OrderHom.lfp_le _ hd).trans inf_le_left

theorem close_cutMod_le_closeR' {m : sh.OpenMod} {Rch : sh.ReachRel}
    {Bad : (y : sh.self.Op) → sh.self.Ar y → Prop} (hpc : ReachPrefixClosed m Rch)
    (hbad : ∀ (y : sh.self.Op) c₁ b s',
      (c₁, .ret b s') ∈ closeR m Rch y.1 y.2.2 y.2.1 → ¬ Bad y (b, s')) :
    close (cutMod m Rch Bad) ≤ closeR m Rch :=
  OrderHom.lfp_le _ ((resolve_cutMod_le hpc hbad).trans (le_of_eq (OrderHom.map_lfp _)))

end Silmaril.Proofs.Games.Abstract.CloseReach
