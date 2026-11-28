module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Defs
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Codes

/-! # Reusable reification and readback for finite constructor codes -/

public section

open Silmaril.Isotope
open Silmaril.Isotope.LetIter.PaperExpression.Source

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite

variable {Φ ε : Type} [HasTy Φ (Ty Unit)] [HasEff Φ ε] [Preorder ε] [OrderBot ε]
  {Γ : EffectCtx (Ty Unit) ε} {c S T B : Code} {C : Ty Unit} {e : ε} {a : Expr Φ}

local notation "slot[" c "]" => (Code.ty c, (⊥ : ε))

omit [HasTy Φ (Ty Unit)] in
theorem literal_subst (c : Code) (x : c.Value) (σ : Nat → Expr Φ) :
    (c.literal x).subst σ = c.literal x :=
  Proofs.literal_subst c x σ

theorem literal_wf (c : Code) (x : c.Value) : Wf Γ (c.literal x : Expr Φ) c.ty e :=
  Proofs.literal_wf c x

omit [HasTy Φ (Ty Unit)] in
theorem dispatch_subst (c : Code) {rows : c.Value → Expr Φ}
    (closed : ∀ v σ, (rows v).subst σ = rows v) (σ : Nat → Expr Φ) :
    (c.dispatch rows a).subst σ = c.dispatch rows (a.subst σ) :=
  Proofs.dispatch_subst c closed σ

theorem dispatch_wf (c : Code) {rows : c.Value → Expr Φ}
    (branches : ∀ {Δ : EffectCtx (Ty Unit) ε} v, Wf Δ (rows v) C e)
    (arg : Wf Γ a c.ty e) : Wf Γ (c.dispatch rows a) C e :=
  Proofs.dispatch_wf c branches arg

theorem dispatch_eqv (c : Code) {rows : c.Value → Expr Φ} {b : Expr Φ}
    (branches : ∀ {Δ : EffectCtx (Ty Unit) ε} v, Wf Δ (rows v) C e)
    (arg : Eqv Γ c.ty e a b) : Eqv Γ C e (c.dispatch rows a) (c.dispatch rows b) :=
  Proofs.dispatch_eqv c branches arg

theorem dispatch_beta (c : Code) (v : c.Value) {rows : c.Value → Expr Φ}
    (closed : ∀ v σ, (rows v).subst σ = rows v)
    (branches : ∀ {Δ : EffectCtx (Ty Unit) ε} v, Wf Δ (rows v) C e) :
    Eqv Γ C e (c.dispatch rows (c.literal v)) (rows v) :=
  Proofs.dispatch_beta c v closed branches

theorem eqv_by_codes (c : Code) {a b : Expr Φ}
    (ha : Wf [(c.ty, ⊥)] a C e) (hb : Wf [(c.ty, ⊥)] b C e)
    (rows : ∀ v : c.Value, Eqv ([] : EffectCtx (Ty Unit) ε) C e
      (a.subst (c.literal v).subst0) (b.subst (c.literal v).subst0)) :
    Eqv [(c.ty, ⊥)] C e a b :=
  Proofs.eqv_by_codes c ha hb rows

theorem stateMap_typed (h : S.Value → T.Value) :
    Wf (slot[S] :: Γ) (stateMap S T h : Expr Φ) T.ty e :=
  Proofs.stateMap_wf h

theorem stateMap_specialize (h : S.Value → T.Value) (s : S.Value) :
    Eqv Γ T.ty e ((stateMap S T h : Expr Φ).subst (S.literal s).subst0) (T.literal (h s)) :=
  Proofs.stateMap_readback h s

omit [HasTy Φ (Ty Unit)] in
theorem stateMap_wk1 {h : S.Value → T.Value} :
    (stateMap S T h : Expr Φ).wk1 = stateMap S T h :=
  Proofs.stateMap_wk1

theorem mapControl_wf (h : S.Value → T.Value) :
    Wf (slot[Code.sum B S] :: Γ) (mapControl (Φ := Φ) B h) (Code.sum B T).ty e :=
  Proofs.mapControl_wf h

omit [HasTy Φ (Ty Unit)] in
theorem mapControl_subst (h : S.Value → T.Value) (σ : Nat → Expr Φ) :
    (mapControl (Φ := Φ) B h).subst σ = .case (σ 0) (.inl (.var 0)) (.inr (stateMap S T h)) :=
  Proofs.mapControl_subst h σ

omit [HasTy Φ (Ty Unit)] in
theorem mapControl_wk1 {h : S.Value → T.Value} :
    (mapControl (Φ := Φ) B h).wk1 = mapControl B h :=
  Proofs.mapControl_wk1

theorem mapControl_readback (h : S.Value → T.Value) (v : (Code.sum B S).Value) :
    Eqv Γ (Code.sum B T).ty e (.let₁ ((Code.sum B S).literal v) (mapControl B h) : Expr Φ)
      ((Code.sum B T).literal (Sum.map id h v)) :=
  Proofs.mapControl_readback h v

theorem finiteValue (c : Code) : _root_.Finite c.Value :=
  Proofs.finiteValue c

theorem encodeFinite (A : Type) [_root_.Finite A] (initial : A) :
    ∃ c : Code, Nonempty (c.Value ≃ A) :=
  Proofs.encodeFinite A initial

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite
