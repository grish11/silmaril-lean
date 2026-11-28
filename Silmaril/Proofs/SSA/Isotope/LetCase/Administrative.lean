module

public import Silmaril.SSA.Isotope.LetCase.Administrative.Defs
public import Silmaril.Raw.SSA.Isotope.LetCase.LocallyNameless.Equiv
public import Silmaril.Raw.SSA.Isotope.LetCase.LocallyNameless.Purity

public section

namespace Silmaril.Isotope.LetCase.LocallyNameless

universe u v w x

variable {ν : Type w} [DecidableEq ν] {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {ε : Type x}
  [HasEff Φ ε]

omit [DecidableEq ν] [TypeFormers τ] [HasTy Φ τ] in
/-- A value is pure. -/
theorem pure_of_isValue_proof (pe : ε) : {n : Nat} → (t : Tm ν Φ n) → t.isValue = true → Pure pe t
  | _, .bv _, _ => .bv
  | _, .unit, _ => .unit
  | _, .pair a b, h => by
    simp only [Tm.isValue, Bool.and_eq_true] at h
    exact .pair (pure_of_isValue_proof pe a h.1) (pure_of_isValue_proof pe b h.2)
  | _, .fv _, h | _, .op _ _, h | _, .let₁ _ _, h | _, .let₂ _ _, h | _, .inl _, h | _, .inr _, h
  | _, .case _ _ _, h | _, .abort _, h => by simp [Tm.isValue] at h

omit [DecidableEq ν] [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] in
/-- A term with a value pair is the pair of two values. -/
theorem valuePair_eq_proof {n : Nat} {t a b : Tm ν Φ n} (h : t.valuePair = some (a, b)) :
    t = .pair a b ∧ a.isValue = true ∧ b.isValue = true := by
  cases t with
  | pair c d =>
    simp only [Tm.valuePair] at h
    split at h
    · rename_i values
      simp only [Bool.and_eq_true] at values
      cases h
      exact ⟨rfl, values⟩
    · cases h
  | _ => simp [Tm.valuePair] at h

omit [HasEff Φ ε] in
/-- A typed pair has a product type, and its components have the types of
some product equal to it. -/
theorem pair_typing_proof {Γ : Isotope.Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {x y : Tm ν Φ n}
    {T : τ} (h : HasType Φ Γ β (.pair x y) T) :
    ∃ A B, T = product A B ∧ HasType Φ Γ β x A ∧ HasType Φ Γ β y B := by
  cases h with
  | pair hx hy => exact ⟨_, _, rfl, hx, hy⟩

/-- One pass of administrative moves keeps the native meaning, when
products of types are injective. -/
theorem administrative_equiv_proof (pe : ε)
    (products : ∀ {A B C D : τ}, product A B = product C D → A = C ∧ B = D)
    {Γ : Isotope.Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {t : Tm ν Φ n} {A : τ} (h : HasType Φ Γ β t A) : Equiv pe Γ β t t.administrative A := by
  induction h with
  | fv h => exact .refl (.fv h)
  | bv => exact .refl .bv
  | op ha ih => exact .op ih
  | let₁ ha hb iha ihb =>
    simp only [Tm.administrative]
    split
    · rename_i value
      exact (Equiv.let₁ (.refl ha) ihb).trans
        (Equiv.letBeta (pure_of_isValue_proof pe _ value) ha ihb.hasType.2)
    · exact .let₁ iha ihb
  | unit => exact .refl .unit
  | pair ha hb iha ihb => exact .pair iha ihb
  | let₂ ha hc iha ihc =>
    simp only [Tm.administrative]
    split
    · rename_i x y found
      obtain ⟨rfl, vx, vy⟩ := valuePair_eq_proof found
      obtain ⟨A', B', eq, hx, hy⟩ := pair_typing_proof ha
      obtain ⟨rfl, rfl⟩ := products eq
      have hc' := ihc.hasType.2
      exact ((Equiv.let₂ (.refl (.pair hx hy)) ihc).trans (Equiv.pairBeta hx hy hc')).trans
        ((Equiv.let₁ (.refl hx)
          (Equiv.letBeta (pure_of_isValue_proof pe _ vy).lift hy.lift hc')).trans
          (Equiv.letBeta (pure_of_isValue_proof pe _ vx) hx (hc'.instantiate hy.lift)))
    · exact .let₂ iha ihc
  | inl ha ih => exact .inl ih
  | inr ha ih => exact .inr ih
  | case he hl hr ihe ihl ihr => exact .case ihe ihl ihr
  | abort ha ih => exact .abort ih

/-- Any number of passes of administrative moves keeps the native meaning. -/
theorem administrative_iterate_proof (pe : ε)
    (products : ∀ {A B C D : τ}, product A B = product C D → A = C ∧ B = D)
    {Γ : Isotope.Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {A : τ} : (passes : Nat) → {t : Tm ν Φ n} → HasType Φ Γ β t A →
    Equiv pe Γ β t (Tm.administrative^[passes] t) A
  | 0, _, h => .refl h
  | passes + 1, _, h =>
    (administrative_equiv_proof pe products h).trans
      (administrative_iterate_proof pe products passes
        (administrative_equiv_proof pe products h).hasType.2)

end Silmaril.Isotope.LetCase.LocallyNameless
