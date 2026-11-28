module

public import Silmaril.SSA.Isotope.LetParCase.Defs
public import Silmaril.SSA.Isotope.LetIter.Defs
public import Silmaril.SSA.Isotope.LetParIter.Semantics.Defs

/-! # LetIter in the shared parallel grammar -/

@[expose] public section

namespace Silmaril.Isotope.LetParIter

open Parallel

universe u v w

/-- The iteration tier of the common parallel syntax. -/
abbrev Tm := Parallel.Tm .iter

scoped infixr:30 " || " => Parallel.Tm.par

theorem hasCase : Tier.HasCase .iter := Tier.iterHasCase rfl

variable {ν : Type v} {Φ : Type w} {n : Nat}

/-- Include the case tier with the same constructors and scoping. -/
def ofLetParCase : LetParCase.Tm ν Φ n → Tm ν Φ n := Parallel.Tm.widen Tier.caseIter

/-- Include the sequential parallel tier through the case tier. -/
def ofLetPar : LetPar.Tm ν Φ n → Tm ν Φ n :=
  ofLetParCase ∘ LetParCase.ofLetPar

/-- Include actual native LetIter syntax. Its sequential product stays sequential. -/
def embed {n : Nat} : LetIter.LocallyNameless.Tm ν Φ n → Tm ν Φ n
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
  | .iter a b => .iter rfl (embed a) (embed b)

/-- Recognize the native fragment, including feedback and excluding parallel pairing. -/
def toLetIter? {n : Nat} : Tm ν Φ n → Option (LetIter.LocallyNameless.Tm ν Φ n)
  | .fv x => some (.fv x)
  | .bv i => some (.bv i)
  | .op f a => return .op f (← toLetIter? a)
  | .let₁ a b => return .let₁ (← toLetIter? a) (← toLetIter? b)
  | .unit => some .unit
  | .pair a b => return .pair (← toLetIter? a) (← toLetIter? b)
  | .let₂ a b => return .let₂ (← toLetIter? a) (← toLetIter? b)
  | .inl _ a => return .inl (← toLetIter? a)
  | .inr _ a => return .inr (← toLetIter? a)
  | .case _ e l r => return .case (← toLetIter? e) (← toLetIter? l) (← toLetIter? r)
  | .abort _ a => return .abort (← toLetIter? a)
  | .iter _ a b => return .iter (← toLetIter? a) (← toLetIter? b)
  | .par _ _ => none

variable {τ : Type u} [TypeFormers τ] [DecidableEq ν] [HasTy Φ τ]
variable {Γ : Ctx ν τ} {β : BoundCtx τ n} {A : τ}

/-- Exact native typing embeds at the same type and in the same two contexts. -/
def derivation : {n : Nat} → {β : BoundCtx τ n} →
    {t : LetIter.LocallyNameless.Tm ν Φ n} → {A : τ} →
    LetIter.LocallyNameless.Derivation Φ Γ β t A → Derivation Φ Γ β (embed t) A
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
  | _, _, _, _, .iter ha hb => .iter (derivation ha) (derivation hb)

/-- Widen case-tier typing, preserving its parallel computations. -/
def ofLetParCaseDerivation : {n : Nat} → {β : BoundCtx τ n} →
    {t : LetParCase.Tm ν Φ n} → {A : τ} →
    Derivation Φ Γ β t A → Derivation Φ Γ β (ofLetParCase t) A
  | _, _, _, _, .fv h => .fv h
  | _, _, _, _, .bv => .bv
  | _, _, _, _, .op ha => .op (ofLetParCaseDerivation ha)
  | _, _, _, _, .let₁ ha hb => .let₁ (ofLetParCaseDerivation ha) (ofLetParCaseDerivation hb)
  | _, _, _, _, .unit => .unit
  | _, _, _, _, .pair ha hb => .pair (ofLetParCaseDerivation ha) (ofLetParCaseDerivation hb)
  | _, _, _, _, .let₂ ha hb => .let₂ (ofLetParCaseDerivation ha) (ofLetParCaseDerivation hb)
  | _, _, _, _, .inl ha => .inl (ofLetParCaseDerivation ha)
  | _, _, _, _, .inr ha => .inr (ofLetParCaseDerivation ha)
  | _, _, _, _, .case he hl hr => .case (ofLetParCaseDerivation he)
      (ofLetParCaseDerivation hl) (ofLetParCaseDerivation hr)
  | _, _, _, _, .abort ha => .abort (ofLetParCaseDerivation ha)
  | _, _, .iter h _ _, _, _ => nomatch h
  | _, _, _, _, .par ha hb => .par (ofLetParCaseDerivation ha) (ofLetParCaseDerivation hb)

/-- Widen sequential-tier typing along the two successive inclusions. -/
def ofLetParDerivation {t : LetPar.Tm ν Φ n} (d : Derivation Φ Γ β t A) :
    Derivation Φ Γ β (ofLetPar t) A :=
  ofLetParCaseDerivation (LetParCase.ofLetParDerivation d)

variable [Subtyping τ]

/-- Regard exact native typing as proof-relevant typing without coercions. -/
def nativeTyping : {n : Nat} → {β : BoundCtx τ n} →
    {t : LetIter.LocallyNameless.Tm ν Φ n} → {A : τ} →
    LetIter.LocallyNameless.Derivation Φ Γ β t A →
    LetIter.ProofRelevant.LocallyNameless.HasType Φ Γ β t A
  | _, _, _, _, .fv h => .fv h
  | _, _, _, _, .bv => .bv
  | _, _, _, _, .op ha => .op (nativeTyping ha)
  | _, _, _, _, .let₁ ha hb => .let₁ (nativeTyping ha) (nativeTyping hb)
  | _, _, _, _, .unit => .unit
  | _, _, _, _, .pair ha hb => .pair (nativeTyping ha) (nativeTyping hb)
  | _, _, _, _, .let₂ ha hb => .let₂ (nativeTyping ha) (nativeTyping hb)
  | _, _, _, _, .inl ha => .inl (nativeTyping ha)
  | _, _, _, _, .inr ha => .inr (nativeTyping ha)
  | _, _, _, _, .case he hl hr => .case (nativeTyping he) (nativeTyping hl) (nativeTyping hr)
  | _, _, _, _, .abort ha => .abort (nativeTyping ha)
  | _, _, _, _, .iter ha hb => .iter (nativeTyping ha) (nativeTyping hb)

end Silmaril.Isotope.LetParIter
