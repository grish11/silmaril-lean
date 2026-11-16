module

public import Silmaril.Logic.Consequence.Gentzen.Calculus.Defs

/-! Proofs for `Silmaril.Logic.Consequence.Gentzen.Calculus.Thms`. -/

@[expose] public section

namespace Silmaril.Proofs.Logic.Consequence.Gentzen.Calculus

open Silmaril.Consequence.Gentzen

universe u

variable {C : Type u} {S : Seq C}

theorem congr_subset (hS : Closed defaultRules S) {Γ Γ' Δ Δ' : List C} (h₁ : Γ ⊆ Γ')
    (h₂ : Γ' ⊆ Γ) (h₃ : Δ ⊆ Δ') (h₄ : Δ' ⊆ Δ) : S Γ Δ ↔ S Γ' Δ' :=
  ⟨hS.weak h₁ h₃, hS.weak h₂ h₄⟩

/-- `NegL` is inverted by `NegR`, reflexivity, cut and weakening. -/
theorem negL_inv {neg : C → C} (hS : Closed defaultRules S) (hR : NegR neg S) {Γ Δ : List C}
    {d : C} (h : S (neg d :: Γ) Δ) : S Γ (d :: Δ) := by
  have h0 : S [d] [d] := hS.refl trivial (List.mem_singleton_self d) (List.mem_singleton_self d)
  have h1 : S [] (neg d :: [d]) := hR h0
  have h2 := hS.cut trivial h1 h
  exact hS.weak (fun x hx => by simpa using hx) (fun x hx => by simpa using hx) h2

/-- `NegR` is inverted by `NegL`, reflexivity, cut and weakening. -/
theorem negR_inv {neg : C → C} (hS : Closed defaultRules S) (hL : NegL neg S) {Γ Δ : List C}
    {g : C} (h : S Γ (neg g :: Δ)) : S (g :: Γ) Δ := by
  have h0 : S [g] [g] := hS.refl trivial (List.mem_singleton_self g) (List.mem_singleton_self g)
  have h1 : S (neg g :: [g]) [] := hL h0
  have h2 := hS.cut trivial h h1
  refine hS.weak ?_ (fun x hx => by simpa using hx) h2
  intro x hx
  simp only [List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | rfl
  · exact List.mem_cons_of_mem _ hx
  · exact List.mem_cons_self

theorem iff_toUnsat {neg : C → C} (hS : Closed defaultRules S) (hL : NegL neg S)
    (hR : NegR neg S) (Γ Δ : List C) : S Γ Δ ↔ toUnsat S (Γ ++ Δ.map neg) := by
  induction Δ generalizing Γ with
  | nil => simp [toUnsat]
  | cons d Δ ih =>
    rw [show S Γ (d :: Δ) ↔ S (neg d :: Γ) Δ from ⟨fun h => hL h, negL_inv hS hR⟩, ih]
    unfold toUnsat
    exact congr_subset hS List.perm_middle.symm.subset
      List.perm_middle.subset (fun _ h => h) (fun _ h => h)

theorem iff_toTaut {neg : C → C} (hS : Closed defaultRules S) (hL : NegL neg S)
    (hR : NegR neg S) (Γ Δ : List C) : S Γ Δ ↔ toTaut S (Γ.map neg ++ Δ) := by
  induction Γ generalizing Δ with
  | nil => simp [toTaut]
  | cons g Γ ih =>
    rw [show S (g :: Γ) Δ ↔ S Γ (neg g :: Δ) from ⟨fun h => hR h, negR_inv hS hL⟩, ih]
    unfold toTaut
    exact congr_subset hS (fun _ h => h) (fun _ h => h)
      List.perm_middle.subset List.perm_middle.symm.subset

/-- The calculus of pure identity: derivable sequents are exactly those sharing a formula. -/
theorem identity_iff_overlap {Γ Δ : List C} :
    Derives defaultRules (⊥ : Seq C) Γ Δ ↔ ∃ x ∈ Γ, x ∈ Δ := by
  constructor
  · intro h
    induction h with
    | base h => exact h.elim
    | refl _ hΓ hΔ => exact ⟨_, hΓ, hΔ⟩
    | weak h₁ h₂ _ ih =>
      obtain ⟨x, hx, hx'⟩ := ih
      exact ⟨x, h₁ hx, h₂ hx'⟩
    | @cut Γ Γ' Δ Δ' a _ _ _ ih₁ ih₂ =>
      obtain ⟨x, hx, hx'⟩ := ih₁
      rcases List.mem_cons.1 hx' with rfl | hx'
      · obtain ⟨y, hy, hy'⟩ := ih₂
        rcases List.mem_cons.1 hy with rfl | hy
        · exact ⟨y, List.mem_append_left _ hx, List.mem_append_right _ hy'⟩
        · exact ⟨y, List.mem_append_right _ hy, List.mem_append_right _ hy'⟩
      · exact ⟨x, List.mem_append_left _ hx, List.mem_append_left _ hx'⟩
  · rintro ⟨x, hx, hx'⟩
    exact .refl trivial hx hx'

theorem empty_iff_universal (hw : WeakSubset S) :
    S [] [] ↔ ∀ Γ Δ, S Γ Δ :=
  ⟨fun h Γ Δ => hw (List.nil_subset Γ) (List.nil_subset Δ) h, fun h => h [] []⟩

theorem valid_negL {M : Type*} {sat : M → C → Prop} {neg : C → C} (hn : NegSound sat neg) :
    NegL neg (Valid sat) := by
  intro Γ Δ d h m hm
  obtain ⟨e, he, hs⟩ := h m fun x hx => hm x (List.mem_cons_of_mem _ hx)
  rcases List.mem_cons.1 he with rfl | he
  · exact absurd hs (hn m e (hm _ List.mem_cons_self))
  · exact ⟨e, he, hs⟩

theorem valid_negR {M : Type*} {sat : M → C → Prop} {neg : C → C} (hn : NegComplete sat neg) :
    NegR neg (Valid sat) := by
  intro Γ Δ g h m hm
  by_cases hg : sat m g
  · obtain ⟨e, he, hs⟩ := h m fun x hx => by
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hg
      · exact hm x hx
    exact ⟨e, List.mem_cons_of_mem _ he, hs⟩
  · exact ⟨neg g, List.mem_cons_self, hn m g hg⟩

end Silmaril.Proofs.Logic.Consequence.Gentzen.Calculus
