module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Substitution.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Packing

/-! # Typed packing and dispatch for finite exit interfaces -/

public section

universe u v w x

namespace Silmaril.Isotope.LambdaSSA.Region

open Silmaril.Isotope (Value)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

theorem HasType.packExits {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ} (hr : HasType Γ r L) :
    HasType Γ r.packExits [packedExitType L] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.packExits_typed hr

/-- Packing is a native forwarding substitution, so it respects the typed
rewrite theory in every input context. -/
theorem RewriteEquiv.packExits {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (h : RewriteEquiv Γ r s L) : RewriteEquiv Γ r.packExits s.packExits [packedExitType L] :=
  h.lsubst (Proofs.SSA.Isotope.LambdaSSA.Rewrite.packExits_forwards Γ L)

theorem unpackExits_hasType (Γ : VCtx τ) (L : LCtx τ) :
    HasType (packedExitType L :: Γ) (unpackExits L : Region Φ) L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.unpackExits_typed Γ L

@[simp] theorem packExits_br {Φ : Type v} (ℓ : Nat) (a : Tm Φ) :
    (Region.br ℓ a).packExits = .br 0 (packedExitArg ℓ a) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.packExits_br ℓ a

/-- Tagging a branch payload preserves the evaluation of its computation. -/
theorem packedExitArg_eval {Φ : Type v} {α : Type w} {σ : Type x}
    {instr : Φ → Value α → σ → Value α → σ → Prop}
    {env : Semantics.Env α} {a : Tm Φ} {start finish : σ} {value : Value α}
    (h : Semantics.Tm.Eval instr env a start value finish) (ℓ : Nat) :
    Semantics.Tm.Eval instr env (packedExitArg ℓ a) start (packedExitValue ℓ value) finish := by
  induction ℓ with
  | zero => exact .inl h
  | succ ℓ ih => exact .inr ih

/-- The native dispatcher decodes any well-typed packed exit without changing state. -/
theorem unpackExits_eval {τ : Type u} {Φ : Type v} {α : Type w} {σ : Type x}
    {instr : Φ → Value α → σ → Value α → σ → Prop}
    {L : LCtx τ} {ℓ : Nat} {A : τ} (hℓ : At L ℓ A)
    (env : Semantics.Env α) (value : Value α) (state : σ) :
    Semantics.Region.Eval instr (Semantics.extend env (packedExitValue ℓ value))
      (unpackExits L) state ℓ value state :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.unpackExits_eval hℓ env value state

end Silmaril.Isotope.LambdaSSA.Region
