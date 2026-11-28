module

public import Silmaril.SSA.Isotope.LetPar.Equations.Defs
public import Silmaril.Raw.SSA.Isotope.LetCase.LocallyNameless.Derivation
public import Silmaril.SSA.Isotope.LetPar.Native.Defs

/-! The exact embedding of the native LetCase calculus. -/

@[expose] public section

namespace Silmaril.Isotope.LetParCase

open Parallel

universe u v w

variable {ν : Type v} {Φ : Type w} {n : Nat}

/-- Case forms are available in the case tier. -/
theorem hasCase : Tier.HasCase .case := by intro h; cases h

/-- Extend the lower parallel tier with case forms. -/
def ofLetPar : LetPar.Tm ν Φ n → Tm ν Φ n := Parallel.Tm.widen Tier.seqCase

/-- Preserve each native constructor, including the original sequential pair. -/
def embed {n : Nat} : LetCase.LocallyNameless.Tm ν Φ n → Tm ν Φ n
  | .fv x => .fv x
  | .bv i => .bv i
  | .op f a => .op f (embed a)
  | .let₁ a b => .let₁ (embed a) (embed b)
  | .unit => .unit
  | .pair a b => .pair (embed a) (embed b)
  | .let₂ a b => .let₂ (embed a) (embed b)
  | .inl a => .inl hasCase (embed a)
  | .inr a => .inr hasCase (embed a)
  | .case e l r => .case hasCase (embed e) (embed l) (embed r)
  | .abort a => .abort hasCase (embed a)

variable {τ : Type u} [TypeFormers τ] [DecidableEq ν] [HasTy Φ τ] {Γ : Ctx ν τ}

/-- Include the native typing data with the very same contexts and result type. -/
def derivation : {n : Nat} → {β : BoundCtx τ n} →
    {t : LetCase.LocallyNameless.Tm ν Φ n} → {A : τ} →
    LetCase.LocallyNameless.Derivation Φ Γ β t A → Parallel.Derivation Φ Γ β (embed t) A
  | _, _, _, _, .fv h => .fv h
  | _, _, _, _, .bv => .bv
  | _, _, _, _, .op ha => .op (derivation ha)
  | _, _, _, _, .let₁ ha hb => .let₁ (derivation ha) (derivation hb)
  | _, _, _, _, .unit => .unit
  | _, _, _, _, .pair ha hb => .pair (derivation ha) (derivation hb)
  | _, _, _, _, .let₂ ha hb => .let₂ (derivation ha) (derivation hb)
  | _, _, _, _, .inl ha => .inl (derivation ha)
  | _, _, _, _, .inr ha => .inr (derivation ha)
  | _, _, _, _, .case he hl hr => .case (derivation he) (derivation hl) (derivation hr)
  | _, _, _, _, .abort ha => .abort (derivation ha)

/-- Include the lower parallel typing evidence, including parallel constructor nodes. -/
def ofLetParDerivation : {n : Nat} → {β : BoundCtx τ n} →
    {t : LetPar.Tm ν Φ n} → {A : τ} →
    Parallel.Derivation Φ Γ β t A → Parallel.Derivation Φ Γ β (ofLetPar t) A
  | _, _, _, _, .fv h => .fv h
  | _, _, _, _, .bv => .bv
  | _, _, _, _, .op ha => .op (ofLetParDerivation ha)
  | _, _, _, _, .let₁ ha hb => .let₁ (ofLetParDerivation ha) (ofLetParDerivation hb)
  | _, _, _, _, .unit => .unit
  | _, _, _, _, .pair ha hb => .pair (ofLetParDerivation ha) (ofLetParDerivation hb)
  | _, _, _, _, .let₂ ha hb => .let₂ (ofLetParDerivation ha) (ofLetParDerivation hb)
  | _, _, .inl h _, _, _ => False.elim (h rfl)
  | _, _, .inr h _, _, _ => False.elim (h rfl)
  | _, _, .case h _ _ _, _, _ => False.elim (h rfl)
  | _, _, .abort h _, _, _ => False.elim (h rfl)
  | _, _, .iter h _ _, _, _ => nomatch h
  | _, _, _, _, .par ha hb => .par (ofLetParDerivation ha) (ofLetParDerivation hb)

end Silmaril.Isotope.LetParCase

@[expose] public section

set_option autoImplicit true

namespace Silmaril.Isotope.Parallel

variable {tier : Tier} {ν : Type u} {Φ : Type v} {ε : Type w} [HasEff Φ ε]

/-- Native case and empty schemes, plus distribution of Par over a pure choice.
The partner is lifted under each arm’s binder. -/
inductive CaseRule (pureEff : ε) : EqScheme tier ν Φ where
  | betaL (h : tier.HasCase) (e : Tm tier ν Φ n) (l r : Tm tier ν Φ (n + 1)) :
      CaseRule pureEff (.case h (.inl h e) l r) (.let₁ e l)
  | betaR (h : tier.HasCase) (e : Tm tier ν Φ n) (l r : Tm tier ν Φ (n + 1)) :
      CaseRule pureEff (.case h (.inr h e) l r) (.let₁ e r)
  | eta (h : tier.HasCase) (e : Tm tier ν Φ n) :
      CaseRule pureEff (.case h e (.inl h (.bv 0)) (.inr h (.bv 0))) e
  | emptyInitial (h : tier.HasCase) (a : Tm tier ν Φ n) (b c : Tm tier ν Φ (n + 1)) :
      CaseRule pureEff (.let₁ (.abort h a) b) (.let₁ (.abort h a) c)
  | bindLetCase (h : tier.HasCase) (e : Tm tier ν Φ n) (l r d : Tm tier ν Φ (n + 1)) :
      CaseRule pureEff (.let₁ (.case h e l r) d)
        (.case h e (.let₁ l d.underBinder) (.let₁ r d.underBinder))
  | bindCase (h : tier.HasCase) (e : Tm tier ν Φ n) (l r : Tm tier ν Φ (n + 1)) :
      CaseRule pureEff (.case h e l r)
        (.let₁ e (.case h (.bv 0) l.underBinder r.underBinder))
  | parCaseLeft (h : tier.HasCase) (he : Pure pureEff e) :
      CaseRule pureEff (.par (.case h e l r) b)
        (.case h e (.par l b.lift) (.par r b.lift))
  | parCaseRight (h : tier.HasCase) (he : Pure pureEff e) :
      CaseRule pureEff (.par a (.case h e l r))
        (.case h e (.par a.lift l) (.par a.lift r))

end Silmaril.Isotope.Parallel

namespace Silmaril.Isotope.LetParCase

/-- The case tier adds the case schemes to the shared sequential and parallel schemes. -/
abbrev Equiv {ν : Type u} {Φ : Type v} {ε : Type w} [HasEff Φ ε] {τ : Type x}
    [TypeFormers τ] [DecidableEq ν] [HasTy Φ τ] (pureEff : ε) (Γ : Ctx ν τ)
    {n : Nat} (β : BoundCtx τ n) (a b : Tm ν Φ n) (A : τ) :=
  Parallel.Equiv pureEff (Parallel.CaseRule pureEff) Γ β a b A

end Silmaril.Isotope.LetParCase
