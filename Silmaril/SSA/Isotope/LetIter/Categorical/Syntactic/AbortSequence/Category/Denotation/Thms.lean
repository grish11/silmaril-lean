module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Iteration.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Tensor.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.Packing.Defs
import Silmaril.Proofs.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.CategoryDenotation

/-! # Projection of native denotations to the repaired model -/

public section

universe u w

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic

open CategoryTheory
open Silmaril.Isotope.LetIter.LocallyNameless (Derivation Tm)
open Silmaril.Thesis.LambdaIter.Syn.SynCat (ValueCat values)

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] (pe : ε)
  [SymmetricPremonoidalCategory (RepairedSynCat (τ := τ) (Φ := Φ) pe)]
  [DistributivePremonoidalCategory (RepairedSynCat (τ := τ) (Φ := Φ) pe)]
  [StrongElgotFreydCategory (repairedValues (τ := τ) (Φ := Φ) pe)]
  [InstructionModel (repairedValues (τ := τ) (Φ := Φ) pe) (typeModel (τ := τ) (Φ := Φ) pe) Φ]

local notation "P" => repairedProjection (τ := τ) (Φ := Φ) pe
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

/-- Projection commutes with native denotation over the shared syntactic value model.
The repaired tensor comparison and the primitive interpretations are explicit. -/
theorem repairedDenote_map {ν : Type w} [DecidableEq ν] {Γ : Ctx ν τ}
    {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ n} {A : τ}
    (d : Derivation Φ Γ β t A) :
    (P).map (denoteInSyntax pe d) = denote Jq model d :=
  DenotationProofs.repairedDenote_map pe tensorHom instr d

/-- In empty free context, projection preserves the packed denotation using the
same packing isomorphism in the common value category. -/
theorem repairedPacked_map {n : Nat} {β : BoundCtx τ n} {t : Tm Empty Φ n} {A : τ}
    (d : Derivation Φ (Ctx.nil : Ctx Empty τ) β t A) :
    (P).map (packedNative pe d) =
      (Jq).map (packedEnvIso (Φ := Φ) pe β).inv ≫ denote Jq model d :=
  DenotationProofs.repairedPacked_map pe tensorHom instr d

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic
