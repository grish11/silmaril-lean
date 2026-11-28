module

public import Silmaril.SSA.Isotope.LetPar.Defs
public import Silmaril.Raw.SSA.Isotope.LetSeq.LocallyNameless.Derivation

/-! The exact embedding of the native LetSeq calculus. -/

@[expose] public section

namespace Silmaril.Isotope.LetPar

open Parallel

universe u v w

variable {ν : Type v} {Φ : Type w} {n : Nat}

/-- Preserve each native constructor, including the original sequential pair. -/
def embed {n : Nat} : LetSeq.LocallyNameless.Tm ν Φ n → Tm ν Φ n
  | .fv x => .fv x
  | .bv i => .bv i
  | .op f a => .op f (embed a)
  | .let₁ a b => .let₁ (embed a) (embed b)
  | .unit => .unit
  | .pair a b => .pair (embed a) (embed b)
  | .let₂ a b => .let₂ (embed a) (embed b)

variable {τ : Type u} [HasProduct τ] [HasUnit τ] [DecidableEq ν] [HasTy Φ τ] {Γ : Ctx ν τ}

/-- Include the native typing data with the very same contexts and result type. -/
def derivation : {n : Nat} → {β : BoundCtx τ n} →
    {t : LetSeq.LocallyNameless.Tm ν Φ n} → {A : τ} →
    LetSeq.LocallyNameless.Derivation Φ Γ β t A → Parallel.Derivation Φ Γ β (embed t) A
  | _, _, _, _, .fv h => .fv h
  | _, _, _, _, .bv => .bv
  | _, _, _, _, .op ha => .op (derivation ha)
  | _, _, _, _, .let₁ ha hb => .let₁ (derivation ha) (derivation hb)
  | _, _, _, _, .unit => .unit
  | _, _, _, _, .pair ha hb => .pair (derivation ha) (derivation hb)
  | _, _, _, _, .let₂ ha hb => .let₂ (derivation ha) (derivation hb)

end Silmaril.Isotope.LetPar
