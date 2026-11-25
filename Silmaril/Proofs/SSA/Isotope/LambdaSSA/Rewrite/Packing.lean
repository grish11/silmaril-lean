module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Substitution.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Thms

/-! # Exact typing of packed and unpacked exits -/

public section

universe u v w x

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region

variable {τ : Type u} [TypeFormers τ] {Φ : Type v}

theorem packedExitArg_value {Γ : VCtx τ} {a : Tm Φ} {A : τ} {L : LCtx τ} {ℓ : Nat}
    (hℓ : At L ℓ A) (ha : Tm.BranchValue Γ a A) :
    Tm.BranchValue Γ (packedExitArg ℓ a) (packedExitType L) := by
  induction L generalizing ℓ with
  | nil => simp [At] at hℓ
  | cons B L ih =>
      cases ℓ with
      | zero =>
          cases Option.some.inj hℓ
          exact .inl ha
      | succ ℓ => exact .inr (ih hℓ)

theorem packExits_forwards (Γ : VCtx τ) (L : LCtx τ) :
    LSubst.Forwards Γ L [packedExitType L] (fun ℓ => .br 0 (packedExitArg ℓ (.var 0 : Tm Φ))) := by
  intro ℓ A hℓ
  exact ⟨0, _, _, rfl, rfl, packedExitArg_value hℓ (.var rfl)⟩

variable [HasTy Φ τ]

theorem packExits_typed {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ} (hr : Region.HasType Γ r L) :
    Region.HasType Γ r.packExits [packedExitType L] := by
  apply hr.lsubst
  intro ℓ A hℓ
  exact .br rfl (packedExitArg_value hℓ (.var (Γ := A :: Γ) rfl)).hasType

theorem unpackExits_typed (Γ : VCtx τ) (L : LCtx τ) :
    Region.HasType (packedExitType L :: Γ) (unpackExits L : Region Φ) L := by
  induction L generalizing Γ with
  | nil =>
      exact .cfg (fun _ => Silmaril.empty) (.br rfl (.var rfl)) (fun _ => .br rfl (.var rfl))
  | cons A L ih =>
      exact .case (.var rfl) (.br rfl (.var rfl))
        ((ih (packedExitType (A :: L) :: Γ)).renameLabels (Silmaril.Isotope.SSA.Ren.wk L A))

theorem packExits_br (ℓ : Nat) (a : Tm Φ) :
    (Region.br ℓ a).packExits = .br 0 (packedExitArg ℓ a) := by
  have h (i : Nat) :
      (packedExitArg i (.var 0 : Tm Φ)).subst (Tm.singleSubst a) = packedExitArg i a := by
    induction i with
    | zero => rfl
    | succ i ih => exact congrArg Tm.inr ih
  exact congrArg (Region.br 0) (h ℓ)

omit [HasTy Φ τ] [TypeFormers τ] in
theorem unpackExits_eval {α : Type w} {σ : Type x}
    {instr : Φ → Value α → σ → Value α → σ → Prop}
    {L : LCtx τ} {ℓ : Nat} {A : τ} (hℓ : At L ℓ A)
    (env : Semantics.Env α) (value : Value α) (state : σ) :
    Semantics.Region.Eval instr (Semantics.extend env (packedExitValue ℓ value))
      (unpackExits L) state ℓ value state := by
  induction L generalizing ℓ env with
  | nil => simp [At] at hℓ
  | cons B L ih =>
      cases ℓ with
      | zero => exact .case_inl .var (.br .var)
      | succ ℓ =>
          exact .case_inr .var
            ((ih hℓ (Semantics.extend env (packedExitValue (ℓ + 1) value))).renameLabels Nat.succ)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
