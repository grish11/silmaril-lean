module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Case.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Flatten.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.SumSplit.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Case

/-! # Original-bound reflection for a pure sum input and effectful arms -/

public section

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless (Tm AbortEquiv)
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Case

universe u v w

section Source

variable {τ : Type u} {Φ : Type v} {ε : Type w}
  [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Preorder ε] [OrderBot ε]
  {Γ : EffectCtx τ ε} {A B C X : τ} {e : ε} {l r l' r' : Expr Φ}

/-- The two checked arms give a checked case at the same bound. -/
theorem source_wf (hl : Wf ((A, (⊥ : ε)) :: Γ) l C e)
    (hr : Wf ((B, (⊥ : ε)) :: Γ) r C e) :
    Wf ((coprod A B, (⊥ : ε)) :: Γ) (onHead l r) C e :=
  Proofs.source_wf hl hr

/-- Substituting the left injection with a free payload exposes the left arm. -/
theorem specialize_left (hl : Wf ((A, (⊥ : ε)) :: Γ) l C e)
    (hr : Wf ((B, (⊥ : ε)) :: Γ) r C e) :
    Eqv ((A, (⊥ : ε)) :: Γ) C e (SumSplit.left 0 (onHead l r)) l :=
  Proofs.specialize_left hl hr

/-- Substituting the right injection with a free payload exposes the right arm. -/
theorem specialize_right (hl : Wf ((A, (⊥ : ε)) :: Γ) l C e)
    (hr : Wf ((B, (⊥ : ε)) :: Γ) r C e) :
    Eqv ((B, (⊥ : ε)) :: Γ) C e (SumSplit.right 0 (onHead l r)) r :=
  Proofs.specialize_right hl hr

/-- Source case equality is equivalent to both arm equations at the supplied bound. -/
theorem eqv_iff_arms (hl : Wf ((A, (⊥ : ε)) :: Γ) l C e)
    (hr : Wf ((B, (⊥ : ε)) :: Γ) r C e)
    (hl' : Wf ((A, (⊥ : ε)) :: Γ) l' C e) (hr' : Wf ((B, (⊥ : ε)) :: Γ) r' C e) :
    Eqv ((coprod A B, (⊥ : ε)) :: Γ) C e (onHead l r) (onHead l' r') ↔
      Eqv ((A, (⊥ : ε)) :: Γ) C e l l' ∧ Eqv ((B, (⊥ : ε)) :: Γ) C e r r' :=
  Proofs.eqv_iff_arms hl hr hl' hr'

end Source

section Reflection

variable {α Φ : Type u} (S : Signature α Φ) {ε : Type w}
  [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε] [DecidableEq α]
  {Γ : EffectCtx (Ty α) ε} {ts : Fin Γ.length → α} {x y c : α} {e : ε}

local notation "Γ₊" => ((Ty.coprod (Ty.base x) (Ty.base y), (⊥ : ε)) :: Γ)
local notation "ΓL" => ((Ty.base x, (⊥ : ε)) :: Γ)
local notation "ΓR" => ((Ty.base y, (⊥ : ε)) :: Γ)

/-- Reflect both arms of a native case equality. Each injection is tested with a free typed
payload, and the straight-line theorem applies in its atomic context. -/
theorem arms_eqv_of_native (hΓ : Γ.Pure) (hs : ∀ i, (Γ.get i).1 = .base (ts i)) (e : ε)
    (l l' : Flatten.Program S (extendSorts x ts) c) (r r' : Flatten.Program S (extendSorts y ts) c)
    (hl : Flatten.Program.WellTyped S e l) (hl' : Flatten.Program.WellTyped S e l')
    (hr : Flatten.Program.WellTyped S e r) (hr' : Flatten.Program.WellTyped S e r')
    {t s : Tm Empty Φ (Γ.length + 1)}
    (ht : (onHead l.source r.source).toLetIter (Γ.length + 1) = some t)
    (ht' : (onHead l'.source r'.source).toLetIter (Γ.length + 1) = some s)
    (hn : letI := S.endpoints
      AbortEquiv (⊥ : ε) (.nil : Ctx Empty (Ty α)) (EffectCtx.toBoundCtx Γ₊) t s (.base c)) :
    letI := S.endpoints
    Eqv ΓL (.base c) e l.source l'.source ∧ Eqv ΓR (.base c) e r.source r'.source :=
  Proofs.arms_eqv_of_native S hΓ hs e l l' r r' hl hl' hr hr' ht ht' hn

/-- Original-bound reflection for a case on the newest pure sum input with atomic payloads, a
pure atomic ambient context, and straight-line arms of atomic result. -/
theorem endpoint_reflection (hΓ : Γ.Pure) (hs : ∀ i, (Γ.get i).1 = .base (ts i)) (e : ε)
    (l l' : Flatten.Program S (extendSorts x ts) c) (r r' : Flatten.Program S (extendSorts y ts) c)
    (hl : Flatten.Program.WellTyped S e l) (hl' : Flatten.Program.WellTyped S e l')
    (hr : Flatten.Program.WellTyped S e r) (hr' : Flatten.Program.WellTyped S e r')
    {t s : Tm Empty Φ (Γ.length + 1)}
    (ht : (onHead l.source r.source).toLetIter (Γ.length + 1) = some t)
    (ht' : (onHead l'.source r'.source).toLetIter (Γ.length + 1) = some s) :
    letI := S.endpoints
    AbortEquiv (⊥ : ε) (.nil : Ctx Empty (Ty α)) (EffectCtx.toBoundCtx Γ₊) t s (.base c) ↔
      Eqv Γ₊ (.base c) e (onHead l.source r.source) (onHead l'.source r'.source) :=
  Proofs.endpoint_reflection S hΓ hs e l l' r r' hl hl' hr hr' ht ht'

end Reflection

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Case
