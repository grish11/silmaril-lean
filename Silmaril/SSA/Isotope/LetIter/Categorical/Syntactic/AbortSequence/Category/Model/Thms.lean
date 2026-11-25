module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Model.Defs
public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Strength.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.ModelReflection.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.CategoryModel

/-! # The abort-extended LetIter syntactic model -/

public section

universe u v

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic

open CategoryTheory
open Silmaril.Isotope.LetIter.LocallyNameless (AbortEquiv Derivation Refinement Tm)
open Silmaril.Thesis.LambdaIter.Syn.SynCat (ValueCat values)

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]
variable (pe : ε)

local notation "S" => signature (τ := τ) (Φ := Φ) pe
local notation "P" => repairedProjection (τ := τ) (Φ := Φ) pe
local notation "Jq" => repairedValues (τ := τ) (Φ := Φ) pe
local notation "M" => typeModel (τ := τ) (Φ := Φ) pe

/-- The quotient model satisfies strong Elgot Freyd laws, including pure uniformity. -/
noncomputable instance repairedStrongElgotFreyd : StrongElgotFreydCategory (Jq) where
  uniformity := by exact ModelProofs.quotientUniformity pe
  iterate_whiskerLeft Z f := by exact repairedIteration_strength pe Z f

/-- Pure instructions factor through the Cartesian value category. -/
theorem repairedInstructionModel_pure (f : Φ) (hf : IsPure pe f) :
    ∃ p : (M).obj (instrSrc f) ⟶ (M).obj (instrTrg f),
      (repairedInstructionModel pe).denote f = (Jq).map p :=
  ModelProofs.repairedInstructionModel_pure pe f hf

/-- In the concrete model, projection preserves the value functor's tensor comparison. -/
theorem repairedTensorComparison_map (R A : ValueCat S) :
    (P).map (Functor.StrongPremonoidal.tensorIso (J := values S) R A).hom =
      (Functor.StrongPremonoidal.tensorIso (J := Jq) R A).hom :=
  (P).map_id _

/-- Interpret a typed native derivation in the abort-extended categorical model. -/
@[expose] noncomputable def repairedDenoteInSyntax {ν : Type v} [DecidableEq ν]
    {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ n} {A : τ}
    (d : Derivation Φ Γ β t A) :
    (Jq).obj (envObj (M) Γ β) ⟶ (Jq).obj ((M).obj A) :=
  letI := repairedInstructionModel (τ := τ) (Φ := Φ) pe
  denote (Jq) (M) d

/-- The concrete quotient denotation is the projection of the exact denotation. -/
theorem repairedDenoteInSyntax_map {ν : Type v} [DecidableEq ν] {Γ : Ctx ν τ}
    {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ n} {A : τ}
    (d : Derivation Φ Γ β t A) :
    (P).map (denoteInSyntax pe d) = repairedDenoteInSyntax pe d := by
  let := repairedInstructionModel (τ := τ) (Φ := Φ) pe
  exact repairedDenote_map pe (repairedTensorComparison_map pe) (fun _ => rfl) d

/-- In empty free context, the concrete model detects precisely the abort-extended relation. -/
theorem repairedDenoteInSyntax_eq_iff {n : Nat} {β : BoundCtx τ n}
    {a b : Tm Empty Φ n} {A : τ}
    (da : Derivation Φ (Ctx.nil : Ctx Empty τ) β a A)
    (db : Derivation Φ (Ctx.nil : Ctx Empty τ) β b A) :
    repairedDenoteInSyntax pe da = repairedDenoteInSyntax pe db ↔
      AbortEquiv pe (Ctx.nil : Ctx Empty τ) β a b A := by
  let := repairedInstructionModel (τ := τ) (Φ := Φ) pe
  exact repairedModel_denote_eq_iff pe (repairedTensorComparison_map pe) (fun _ => rfl) da db

/-- The repaired denotation is judgment-coherent at the empty free context. -/
theorem repairedDenoteInSyntax_typing_nil {n : Nat} {β : BoundCtx τ n}
    {t : Tm Empty Φ n} {A : τ}
    (d e : Derivation Φ (Ctx.nil : Ctx Empty τ) β t A) :
    repairedDenoteInSyntax pe d = repairedDenoteInSyntax pe e :=
  (repairedDenoteInSyntax_eq_iff pe d e).mpr (Refinement.equiv (.refl d.toHasType))

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic
