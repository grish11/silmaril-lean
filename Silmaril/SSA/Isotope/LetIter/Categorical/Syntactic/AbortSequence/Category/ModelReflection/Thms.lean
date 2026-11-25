module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Denotation.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Reflection.Thms

/-! # Reflection for native denotation in a compatible repaired model -/

public section

universe u

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic

open CategoryTheory
open Silmaril.Isotope.LetIter.LocallyNameless (AbortEquiv Derivation Tm)
open Silmaril.Thesis.LambdaIter.Syn.SynCat (ValueCat values)

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] (pe : ε)
  [SymmetricPremonoidalCategory (RepairedSynCat (τ := τ) (Φ := Φ) pe)]
  [DistributivePremonoidalCategory (RepairedSynCat (τ := τ) (Φ := Φ) pe)]
  [StrongElgotFreydCategory (repairedValues (τ := τ) (Φ := Φ) pe)]
  [InstructionModel (repairedValues (τ := τ) (Φ := Φ) pe) (typeModel (τ := τ) (Φ := Φ) pe) Φ]

local notation "Jq" => repairedValues (τ := τ) (Φ := Φ) pe
local notation "model" => typeModel (τ := τ) (Φ := Φ) pe

variable
  (tensorHom : ∀ R A : ValueCat (signature (τ := τ) (Φ := Φ) pe),
    (repairedProjection pe).map
      (Functor.StrongPremonoidal.tensorIso (J := values (signature pe)) R A).hom =
    (Functor.StrongPremonoidal.tensorIso (J := repairedValues pe) R A).hom)
  (instr : ∀ f : Φ, (repairedProjection pe).map ((instructionModel (τ := τ) pe).denote f) =
    InstructionModel.denote (J := repairedValues pe) (M := typeModel (τ := τ) (Φ := Φ) pe) f)

include tensorHom instr

/-- Native denotation in a compatible repaired model detects exactly abort
equivalence at empty free context and arbitrary finite bound context. -/
theorem repairedModel_denote_eq_iff {n : Nat} {β : BoundCtx τ n} {a b : Tm Empty Φ n} {A : τ}
    (da : Derivation Φ (Ctx.nil : Ctx Empty τ) β a A)
    (db : Derivation Φ (Ctx.nil : Ctx Empty τ) β b A) :
    denote Jq model da = denote Jq model db ↔ AbortEquiv pe (Ctx.nil : Ctx Empty τ) β a b A := by
  rw [← repairedProjection_packedNative_eq_iff pe da db, repairedPacked_map pe tensorHom instr da,
    repairedPacked_map pe tensorHom instr db]
  exact (cancel_epi ((Jq).map (packedEnvIso (Φ := Φ) pe β).inv)).symm

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic
