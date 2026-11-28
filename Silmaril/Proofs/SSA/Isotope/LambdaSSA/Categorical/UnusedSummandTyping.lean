module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.UnusedSummand.Defs

/-! # Exact typing of tagged rows under captures and reply binders -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandTyping

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical.UnusedSummand

variable {κ : Type u} {Φ : Type v} [HasTy Φ (Ty κ)]

theorem operand_base {Γ : VCtx (Ty κ)} {A : Ty κ} (a : Operand (Φ := Φ) Γ A) :
    a.term.HasType Γ A := by
  induction a with
  | var _ h => exact .var h
  | unit => exact .unit
  | op _ _ ih => exact .op ih
  | let₁ _ _ iha ihb => exact .let₁ iha ihb
  | pair _ _ iha ihb => exact .pair iha ihb
  | let₂ _ _ iha ihb => exact .let₂ iha ihb

theorem operand_typed {Γ Δ : VCtx (Ty κ)} {ρ : Nat → Nat} (ren : Ren Γ Δ ρ)
    {A : Ty κ} (a : Operand (Φ := Φ) Γ A) : (a.term.rename ρ).HasType Δ A := by
  induction a generalizing Δ ρ with
  | var i h => exact .var (ren h)
  | unit => exact .unit
  | op p _ ih => exact .op (ih ren)
  | let₁ _ _ iha ihb => exact .let₁ (iha ren) (ihb (ren.lift _))
  | pair _ _ iha ihb => exact .pair (iha ren) (ihb ren)
  | let₂ _ _ iha ihb => exact .let₂ (iha ren) (ihb ((ren.lift _).lift _))

theorem operand_type {Γ Δ : VCtx (Ty κ)} {ρ : Nat → Nat} (ren : Ren Γ Δ ρ)
    {A : Ty κ} (a : Operand (Φ := Φ) Γ A) : TypeDetermined Δ (a.term.rename ρ) A := by
  induction a generalizing Δ ρ with
  | var i h =>
      intro D typed
      cases typed with
      | var hit => exact Option.some.inj (hit.symm.trans (ren h))
  | unit =>
      intro D typed
      cases typed
      rfl
  | op p _ =>
      intro D typed
      cases typed
      rfl
  | let₁ value body ihv ihb =>
      intro D typed
      cases typed with
      | let₁ hv hb =>
          cases ihv ren _ hv
          exact ihb (ren.lift _) _ hb
  | pair left right ihl ihr =>
      intro D typed
      cases typed with
      | pair hl hr => rw [ihl ren _ hl, ihr ren _ hr]
  | let₂ value body ihv ihb =>
      intro D typed
      cases typed with
      | let₂ hv hb =>
          obtain ⟨rfl, rfl⟩ := Ty.product.inj (ihv ren _ hv)
          exact ihb ((ren.lift _).lift _) _ hb

theorem operand_determined {Γ Δ : VCtx (Ty κ)} {ρ : Nat → Nat} (ren : Ren Γ Δ ρ)
    {A : Ty κ} (a : Operand (Φ := Φ) Γ A) : DeterminedTerm Δ (a.term.rename ρ) A := by
  induction a generalizing Δ ρ with
  | var i h => exact .var (ren h)
  | unit => exact .unit
  | op p _ ih => exact .op (ih ren)
  | let₁ value _ iha ihb =>
      exact .let₁ (operand_type ren value) (iha ren) (ihb (ren.lift _))
  | pair _ _ iha ihb => exact .pair (iha ren) (ihb ren)
  | let₂ value _ iha ihb =>
      exact .let₂ (operand_type ren value) (iha ren) (ihb ((ren.lift _).lift _))

theorem local_label {n : Nat} (R : Fin n → Ty κ) (i : Fin n) :
    At (List.ofFn R) i (R i) := by
  simp [At]

theorem local_append {n : Nat} (R : Fin n → Ty κ) (L : LCtx (Ty κ)) (i : Fin n) :
    At (List.ofFn R ++ L) i (R i) := by
  have h : i.val < (List.ofFn R).length := by simp
  simpa only [At, List.getElem?_append_left h] using local_label R i

theorem exit_append {n : Nat} (R : Fin n → Ty κ) {L : LCtx (Ty κ)} {i : Nat} {A : Ty κ}
    (h : At L i A) : At (List.ofFn R ++ L) (n + i) A := by
  have bound : (List.ofFn R).length ≤ n + i := by simp
  rw [At, List.getElem?_append_right bound, List.length_ofFn, Nat.add_sub_cancel_left]
  exact h

theorem row_typed {n : Nat} {R : Fin n → Ty κ} {L : LCtx (Ty κ)} {Γ Δ : VCtx (Ty κ)}
    {ρ : Nat → Nat} (ren : Ren Γ Δ ρ) (tails : Option (Fin n → Ty κ)) (r : Row (Φ := Φ) R L Γ) :
    (r.region tails.isSome ρ).HasType Δ (List.ofFn (family R tails) ++ L) := by
  induction r generalizing Δ ρ with
  | jump i arg =>
    cases tails with
    | none => exact .br (local_append R L i) (operand_typed ren arg)
    | some D => exact .br (local_append (family R (some D)) L i) (.inl (operand_typed ren arg))
  | exit i hit arg => exact .br (exit_append (family R tails) hit) (operand_typed ren arg)
  | let₁ value _ ih => exact .let₁ (operand_typed ren value) (ih (ren.lift _))
  | let₂ value _ ih => exact .let₂ (operand_typed ren value) (ih ((ren.lift _).lift _))
  | case arg l r ihl ihr =>
    exact .case (operand_typed ren arg) (ihl (ren.lift _)) (ihr (ren.lift _))

theorem row_determined {n : Nat} {R : Fin n → Ty κ} {L : LCtx (Ty κ)} {Γ Δ : VCtx (Ty κ)}
    {ρ : Nat → Nat} (ren : Ren Γ Δ ρ) (tails : Option (Fin n → Ty κ)) (r : Row (Φ := Φ) R L Γ) :
    DeterminedRegion Δ (r.region tails.isSome ρ) (List.ofFn (family R tails) ++ L) := by
  induction r generalizing Δ ρ with
  | jump i arg =>
    cases tails with
    | none => exact .br (local_append R L i) (operand_determined ren arg)
    | some D => exact .br (local_append (family R (some D)) L i) (.inl (operand_determined ren arg))
  | exit i hit arg => exact .br (exit_append (family R tails) hit) (operand_determined ren arg)
  | let₁ value _ ih =>
      exact .let₁ (operand_type ren value) (operand_determined ren value) (ih (ren.lift _))
  | let₂ value _ ih =>
      exact .let₂ (operand_type ren value) (operand_determined ren value) (ih ((ren.lift _).lift _))
  | case arg l r ihl ihr =>
    exact .case (operand_type ren arg) (operand_determined ren arg) (ihl (ren.lift _)) (ihr (ren.lift _))

theorem program_typed {n : Nat} {R : Fin n → Ty κ} {L : LCtx (Ty κ)} {Γ : VCtx (Ty κ)}
    (p : Program (Φ := Φ) R L Γ) (tails : Option (Fin n → Ty κ)) :
    (p.region tails.isSome).HasType Γ L :=
  .cfg (family R tails) (row_typed (Ren.id Γ) tails p.entry)
    (fun i => row_typed (Ren.wk Γ (family R tails i)) tails (p.blocks i))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandTyping
