module

public import Silmaril.SSA.Isotope.Institution.Ordered.Thms
public import Silmaril.SSA.Isotope.LetCase.Thms

/-! # Opt-in exact LetCase empty sequencing -/

@[expose] public section

namespace Silmaril.Isotope.LetCase.LocallyNameless

universe u v w r

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ν : Type w} [DecidableEq ν]

/-- Explicit sequencing of an empty-typed scrutinee in either direction.
No purity premise is imposed on the scrutinee. -/
inductive AbortSequence (Γ : Ctx ν τ) : TypedRelation ν Φ τ where
  | sequence {n : Nat} {β : BoundCtx τ n} {a : Tm ν Φ n} {A : τ}
      (ha : HasType Φ Γ β a Silmaril.empty) :
      AbortSequence Γ β (.abort a) (.let₁ a (.abort (.bv 0))) A
  | unsequence {n : Nat} {β : BoundCtx τ n} {a : Tm ν Φ n} {A : τ}
      (ha : HasType Φ Γ β a Silmaril.empty) :
      AbortSequence Γ β (.let₁ a (.abort (.bv 0))) (.abort a) A

set_option backward.isDefEq.respectTransparency false in
set_option autoImplicit true in
/-- The new rule alone, closed under exact constructor congruence. Its
witnesses record intermediate typings for the categorical interpretation. -/
inductive AbortCongr (Γ : Ctx ν τ) :
    {n : Nat} → {β : BoundCtx τ n} → {a b : Tm ν Φ n} → {A : τ} →
    Derivation Φ Γ β a A → Derivation Φ Γ β b A → Prop where
  | refl (a : Derivation Φ Γ β t A) : AbortCongr Γ a a
  | symm : AbortCongr Γ a b → AbortCongr Γ b a
  | trans : AbortCongr Γ a b → AbortCongr Γ b c → AbortCongr Γ a c
  | sequence {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ n} {A : τ}
      (a : Derivation Φ Γ β t Silmaril.empty) :
      AbortCongr Γ (.abort (C := A) a)
        (.let₁ a (.abort (C := A) (Derivation.bv (Φ := Φ) (Γ := Γ) (β := β.snoc (empty : τ)) (ι := 0))))
  | op {n : Nat} {β : BoundCtx τ n} {a b : Tm ν Φ n} {f : Φ}
      {da : Derivation Φ Γ β a (instrSrc f)} {db : Derivation Φ Γ β b (instrSrc f)} :
      AbortCongr Γ da db → AbortCongr Γ (.op da) (.op db)
  | let₁ {n : Nat} {β : BoundCtx τ n} {a b : Tm ν Φ n} {c d : Tm ν Φ (n + 1)} {A B : τ}
      {da : Derivation Φ Γ β a A} {db : Derivation Φ Γ β b A}
      {dc : Derivation Φ Γ (β.snoc A) c B} {dd : Derivation Φ Γ (β.snoc A) d B} :
      AbortCongr Γ da db → AbortCongr Γ dc dd → AbortCongr Γ (.let₁ da dc) (.let₁ db dd)
  | let₂ {n : Nat} {β : BoundCtx τ n} {a b : Tm ν Φ n} {c d : Tm ν Φ (n + 2)} {A B C : τ}
      {da : Derivation Φ Γ β a (product A B)} {db : Derivation Φ Γ β b (product A B)}
      {dc : Derivation Φ Γ ((β.snoc A).snoc B) c C} {dd : Derivation Φ Γ ((β.snoc A).snoc B) d C} :
      AbortCongr Γ da db → AbortCongr Γ dc dd → AbortCongr Γ (.let₂ da dc) (.let₂ db dd)
  | pair {n : Nat} {β : BoundCtx τ n} {a b c d : Tm ν Φ n} {A B : τ}
      {da : Derivation Φ Γ β a A} {db : Derivation Φ Γ β b A}
      {dc : Derivation Φ Γ β c B} {dd : Derivation Φ Γ β d B} :
      AbortCongr Γ da db → AbortCongr Γ dc dd → AbortCongr Γ (.pair da dc) (.pair db dd)
  | inl {n : Nat} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A B : τ}
      {da : Derivation Φ Γ β a A} {db : Derivation Φ Γ β b A} :
      AbortCongr Γ da db → AbortCongr Γ (.inl (B := B) da) (.inl (B := B) db)
  | inr {n : Nat} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A B : τ}
      {da : Derivation Φ Γ β a B} {db : Derivation Φ Γ β b B} :
      AbortCongr Γ da db → AbortCongr Γ (.inr (A := A) da) (.inr (A := A) db)
  | case {n : Nat} {β : BoundCtx τ n} {a b : Tm ν Φ n} {l l' r r' : Tm ν Φ (n + 1)} {A B C : τ}
      {da : Derivation Φ Γ β a (coprod A B)} {db : Derivation Φ Γ β b (coprod A B)}
      {dl : Derivation Φ Γ (β.snoc A) l C} {dl' : Derivation Φ Γ (β.snoc A) l' C}
      {dr : Derivation Φ Γ (β.snoc B) r C} {dr' : Derivation Φ Γ (β.snoc B) r' C} :
      AbortCongr Γ da db → AbortCongr Γ dl dl' → AbortCongr Γ dr dr' →
      AbortCongr Γ (.case da dl dr) (.case db dl' dr')
  | abort {n : Nat} {β : BoundCtx τ n} {a b : Tm ν Φ n} {C : τ}
      {da : Derivation Φ Γ β a empty} {db : Derivation Φ Γ β b empty} :
      AbortCongr Γ da db → AbortCongr Γ (.abort (C := C) da) (.abort (C := C) db)

variable {ε : Type r} [HasEff Φ ε]

/-- The native theory extended by the two typed empty-sequencing rules. -/
abbrev AbortEquiv (pe : ε) (Γ : Ctx ν τ) : TypedRelation ν Φ τ :=
  Refinement pe Γ (AbortSequence Γ)

end Silmaril.Isotope.LetCase.LocallyNameless
