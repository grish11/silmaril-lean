module

public import Silmaril.Proofs.Games.Abstract.SessionLinkCoh.Basic

/-!
# Coherence of linking sessions: naturality (proofs)

`linkS` commutes with transport of either store: a served round of `mapStore e t` from `s` is a
served round of `t` from `e.symm s`, and a round of `mapStore e' u` at `s'` is a round of `u` at
`e'.symm s'`. Saturating the server or the client, and dropping the plain traps of a saturated
server, do not change the linked triple.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.SessionLinkCoh

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
  Silmaril.Games.Abstract.StratThread Silmaril.Games.Abstract.SessionLink
  Silmaril.Games.Abstract.SessionLinkAssoc

universe u

variable {E : Sig.{u}} {S S' T T' A B A' B' : Type u}

theorem mapEnd_linkEnd_left (e : S ≃ T) (s : S) (x : End S' B') :
    mapEnd (Equiv.prodCongr e (Equiv.refl S')) (linkEnd s x) = linkEnd (e s) x := by
  cases x <;> rfl

theorem mapEnd_linkEnd_right (e : S' ≃ T') (s : S) (x : End S' B') :
    mapEnd (Equiv.prodCongr (Equiv.refl S) e) (linkEnd s x) = linkEnd s (mapEnd e x) := by
  cases x <;> rfl

/-! ## Naturality in the server store -/

theorem apply_prodCongr_symm_fst (e : S ≃ T) (σ : T × S') :
    e ((Equiv.prodCongr e (Equiv.refl S')).symm σ).1 = σ.1 :=
  e.apply_symm_apply σ.1

theorem linkS_mapStore_left (e : S ≃ T) (t : ObsTriple E S A (B ⊕ PUnit.{u + 1}))
    (u : ObsTriple (sig1 A B) S' A' (B' ⊕ PUnit.{u + 1})) :
    linkS (mapStore e t) u = mapStore (Equiv.prodCongr e (Equiv.refl S')) (linkS t u) := by
  refine obsTriple_ext (fun σ a' x => ?_) (fun σ a' x => ?_) (fun σ a' ω => ?_)
  · rw [mem_mapStore_fst]
    obtain ⟨c, en⟩ := x
    constructor
    · rintro (⟨rs, s₁, e₁, hr, hu, hx⟩ | ⟨rs, s₁, a, c', hr, hu, hd, hx⟩ |
        ⟨ω, hω, l, st, n, hs, hn, hx⟩)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hx
        refine Or.inl ⟨rs, e.symm s₁, e₁, rounds_mapStore.1 hr, hu, ?_⟩
        exact Prod.ext rfl (mapEnd_linkEnd_left e.symm s₁ e₁)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hx
        exact Or.inr (Or.inl ⟨rs, e.symm s₁, a, c', rounds_mapStore.1 hr, hu,
          mem_mapStore_div.1 hd, rfl⟩)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hx
        exact Or.inr (Or.inr ⟨ω, hω, l, _, n, infServe_mapStore_of hs, hn, rfl⟩)
    · rintro (⟨rs, s₁, e₁, hr, hu, hx⟩ | ⟨rs, s₁, a, c', hr, hu, hd, hx⟩ |
        ⟨ω, hω, l, st, n, hs, hn, hx⟩)
      · obtain ⟨rfl, hx⟩ := Prod.mk.inj hx
        refine Or.inl ⟨rs, e s₁, e₁, rounds_mapStore.2 (by simpa using hr), hu, ?_⟩
        rw [← mapEnd_linkEnd_left, ← hx]
        exact Prod.ext rfl (mapEnd_mapEnd_symm _ en).symm
      · obtain ⟨rfl, hx⟩ := Prod.mk.inj hx
        refine Or.inr (Or.inl ⟨rs, e s₁, a, c', rounds_mapStore.2 (by simpa using hr), hu,
          mem_mapStore_div.2 (by simpa using hd), ?_⟩)
        rw [← mapEnd_mapEnd_symm (Equiv.prodCongr e (Equiv.refl S')) en, hx]
        rfl
      · obtain ⟨rfl, hx⟩ := Prod.mk.inj hx
        have hs' := infServe_mapStore_to (e := e) hs
        rw [apply_prodCongr_symm_fst] at hs'
        refine Or.inr (Or.inr ⟨ω, hω, l, _, n, hs', hn, ?_⟩)
        rw [← mapEnd_mapEnd_symm (Equiv.prodCongr e (Equiv.refl S')) en, hx]
        rfl
  · constructor
    · rintro ⟨rs, s₁, a, c, hr, hu, hc, hx⟩
      rw [satP_mapStore] at hc
      exact ⟨rs, e.symm s₁, a, c, rounds_mapStore.1 hr, hu, hc, hx⟩
    · rintro ⟨rs, s₁, a, c, hr, hu, hc, hx⟩
      refine ⟨rs, e s₁, a, c, rounds_mapStore.2 (by simpa using hr), hu, ?_, hx⟩
      rw [satP_mapStore]
      simpa using hc
  · constructor
    · rintro (⟨rs, s₁, a, ω', hr, hu, hω', hk⟩ | ⟨ω', hω', l, st, hs, hinf, hk⟩)
      · exact Or.inl ⟨rs, e.symm s₁, a, ω', rounds_mapStore.1 hr, hu, hω', hk⟩
      · exact Or.inr ⟨ω', hω', l, _, infServe_mapStore_of hs, hinf, hk⟩
    · rintro (⟨rs, s₁, a, ω', hr, hu, hω', hk⟩ | ⟨ω', hω', l, st, hs, hinf, hk⟩)
      · refine Or.inl ⟨rs, e s₁, a, ω', rounds_mapStore.2 (by simpa using hr), hu, ?_, hk⟩
        change ω' ∈ t.2.2 (e.symm (e s₁)) a
        simpa using hω'
      · have hs' := infServe_mapStore_to (e := e) hs
        rw [apply_prodCongr_symm_fst] at hs'
        exact Or.inr ⟨ω', hω', l, _, hs', hinf, hk⟩

/-! ## Naturality in the client store -/

theorem linkS_mapStore_right (e : S' ≃ T') (t : ObsTriple E S A (B ⊕ PUnit.{u + 1}))
    (u : ObsTriple (sig1 A B) S' A' (B' ⊕ PUnit.{u + 1})) :
    linkS t (mapStore e u) = mapStore (Equiv.prodCongr (Equiv.refl S) e) (linkS t u) := by
  refine obsTriple_ext (fun σ a' x => ?_) (fun σ a' x => ?_) (fun σ a' ω => ?_)
  · rw [mem_mapStore_fst]
    obtain ⟨c, en⟩ := x
    constructor
    · rintro (⟨rs, s₁, e₁, hr, hu, hx⟩ | ⟨rs, s₁, a, c', hr, hu, hd, hx⟩ |
        ⟨ω, hω, l, st, n, hs, hn, hx⟩)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hx
        refine Or.inl ⟨rs, s₁, _, hr, mem_mapStore_fst.1 hu, ?_⟩
        exact Prod.ext rfl (mapEnd_linkEnd_right e.symm s₁ e₁)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hx
        rw [satP_mapStore] at hu
        exact Or.inr (Or.inl ⟨rs, s₁, a, c', hr, hu, hd, rfl⟩)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hx
        exact Or.inr (Or.inr ⟨ω, hω, l, st, n, hs, hn, rfl⟩)
    · rintro (⟨rs, s₁, e₁, hr, hu, hx⟩ | ⟨rs, s₁, a, c', hr, hu, hd, hx⟩ |
        ⟨ω, hω, l, st, n, hs, hn, hx⟩)
      · obtain ⟨rfl, hx⟩ := Prod.mk.inj hx
        refine Or.inl ⟨rs, s₁, mapEnd e e₁, hr, mem_mapStore_fst.2 (by simpa using hu), ?_⟩
        rw [← mapEnd_linkEnd_right, ← hx]
        exact Prod.ext rfl (mapEnd_mapEnd_symm _ en).symm
      · obtain ⟨rfl, hx⟩ := Prod.mk.inj hx
        refine Or.inr (Or.inl ⟨rs, s₁, a, c', hr, by rw [satP_mapStore]; exact hu, hd, ?_⟩)
        rw [← mapEnd_mapEnd_symm (Equiv.prodCongr (Equiv.refl S) e) en, hx]
        rfl
      · obtain ⟨rfl, hx⟩ := Prod.mk.inj hx
        refine Or.inr (Or.inr ⟨ω, hω, l, st, n, hs, hn, ?_⟩)
        rw [← mapEnd_mapEnd_symm (Equiv.prodCongr (Equiv.refl S) e) en, hx]
        rfl
  · constructor
    · rintro ⟨rs, s₁, a, c, hr, hu, hc, hx⟩
      rw [satP_mapStore] at hu
      exact ⟨rs, s₁, a, c, hr, hu, hc, hx⟩
    · rintro ⟨rs, s₁, a, c, hr, hu, hc, hx⟩
      exact ⟨rs, s₁, a, c, hr, by rw [satP_mapStore]; exact hu, hc, hx⟩
  · constructor
    · rintro (⟨rs, s₁, a, ω', hr, hu, hω', hk⟩ | ⟨ω', hω', l, st, hs, hinf, hk⟩)
      · rw [satP_mapStore] at hu
        exact Or.inl ⟨rs, s₁, a, ω', hr, hu, hω', hk⟩
      · exact Or.inr ⟨ω', hω', l, st, hs, hinf, hk⟩
    · rintro (⟨rs, s₁, a, ω', hr, hu, hω', hk⟩ | ⟨ω', hω', l, st, hs, hinf, hk⟩)
      · exact Or.inl ⟨rs, s₁, a, ω', hr, by rw [satP_mapStore]; exact hu, hω', hk⟩
      · exact Or.inr ⟨ω', hω', l, st, hs, hinf, hk⟩

/-! ## Saturation and plain traps under `linkS` -/

theorem linkS_sat_right (t : ObsTriple E S A (B ⊕ PUnit.{u + 1}))
    (u : ObsTriple (sig1 A B) S' A' (B' ⊕ PUnit.{u + 1})) :
    linkS t (sat u) = linkS t u := by
  have h : satP (sat u) = satP u := congrArg (fun t => t.2.1) (sat_idem (t := u))
  unfold linkS
  rw [h]
  rfl

theorem linkS_dropTrap_sat_left (t : ObsTriple E S A (B ⊕ PUnit.{u + 1}))
    (u : ObsTriple (sig1 A B) S' A' (B' ⊕ PUnit.{u + 1})) :
    linkS (dropTrap (sat t)) u = linkS t u := by
  have hret : ∀ s a c b s₁, (c, End.ret b s₁) ∈ (dropTrap (sat t)).1 s a ↔
      (c, End.ret b s₁) ∈ t.1 s a := fun _ _ _ _ _ =>
    ⟨fun h => h.1, fun h => ⟨h, by simp⟩⟩
  have hdiv : ∀ s a c, (c, End.div) ∈ (dropTrap (sat t)).1 s a ↔ (c, End.div) ∈ t.1 s a :=
    fun _ _ _ => ⟨fun h => h.1, fun h => ⟨h, by simp⟩⟩
  have hidem : satP (sat t) = satP t := congrArg (fun t => t.2.1) (sat_idem (t := t))
  have hsat : satP (dropTrap (sat t)) = satP t := by
    funext s a
    ext x
    constructor
    · rintro (h | ⟨d, m', h, hc⟩ | ⟨d, en, h, hc⟩ | ⟨ω, h, hk⟩)
      · exact h
      · rw [← hidem]; exact Or.inr (Or.inl ⟨d, m', h, hc⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨d, en, h.1, hc⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨ω, h, hk⟩))
    · exact fun h => Or.inl h
  unfold linkS
  rw [rounds_congr hret, infServe_congr hret, hsat]
  simp only [hdiv]
  rfl

end Silmaril.Proofs.Games.Abstract.SessionLinkCoh
