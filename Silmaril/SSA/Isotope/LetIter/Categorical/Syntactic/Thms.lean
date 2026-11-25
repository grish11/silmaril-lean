module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.Defs
public import Silmaril.SSA.Thesis.SyntacticCategory.Packing.Defs
import Silmaril.Proofs.SSA.Isotope.LetIter.Categorical.Syntactic

/-! # Coproduct and purity laws for the native syntactic interpretation -/

public section

universe u

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Thesis.LambdaIter.Syn.SynCat

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]

/-- The type interpretation sends the left syntax injection to the selected value injection. -/
theorem valueInl_coprodIso (pe : ε) (A B : τ) :
    (valueCofan (valueObj (Φ := Φ) pe A) (valueObj pe B)).inl ≫
      ((typeModel (Φ := Φ) pe).coprodIso A B).hom = coprod.inl :=
  valueInl_coprodIso_proof pe A B

/-- The type interpretation sends the right syntax injection to the selected value injection. -/
theorem valueInr_coprodIso (pe : ε) (A B : τ) :
    (valueCofan (valueObj (Φ := Φ) pe A) (valueObj pe B)).inr ≫
      ((typeModel (Φ := Φ) pe).coprodIso A B).hom = coprod.inr :=
  valueInr_coprodIso_proof pe A B

/-- A pure primitive instruction lies in the syntactic value subcategory. -/
theorem instruction_isPure (pe : ε) (f : Φ) (hf : IsPure pe f) :
    IsPureMor ((instructionModel (τ := τ) pe).denote f) :=
  instruction_isPure_proof pe f hf

/-- The copied type coproduct agrees with the chosen computation coproduct through the
value inclusion and its coproduct comparison. -/
theorem map_coprodIso (pe : ε) (A B : τ) :
    let J := values (signature (τ := τ) (Φ := Φ) pe)
    J.map ((typeModel (Φ := Φ) pe).coprodIso A B).hom ≫
      inv (coprodComparison J (valueObj pe A) (valueObj pe B)) =
        (copIso (J.obj (valueObj pe A)) (J.obj (valueObj pe B))).hom :=
  map_coprodIso_proof pe A B

/-- The interpreted bound context has the same object as the packed syntax context. -/
theorem boundObj_eq (pe : ε) {n : Nat} (β : BoundCtx τ n) :
    boundObj (typeModel (Φ := Φ) pe) β =
      valueObj pe (packType (S := signature (τ := τ) (Φ := Φ) pe) (Bridge.BoundCtx.toThesis β)) :=
  boundObj_eq_proof pe β

/-- The empty free context contributes the tensor unit to the bound-context object. -/
noncomputable def packedEnvIso (pe : ε) {n : Nat} (β : BoundCtx τ n) :
    envObj (typeModel (Φ := Φ) pe) (Ctx.nil : Ctx Empty τ) β ≅
      valueObj pe (packType (S := signature (τ := τ) (Φ := Φ) pe) (Bridge.BoundCtx.toThesis β)) :=
  (λ_ (boundObj (typeModel (Φ := Φ) pe) β)).trans (eqToIso (boundObj_eq pe β))

/-- Pure terms, including terms in open contexts, denote pure syntactic arrows. -/
theorem denote_isPure {ν : Type u} [DecidableEq ν] (pe : ε)
    {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {t : LocallyNameless.Tm ν Φ n} {A : τ}
    (d : LocallyNameless.Derivation Φ Γ β t A) (h : LocallyNameless.Pure pe t) :
    letI := instructionModel (τ := τ) (Φ := Φ) pe
    IsPureMor (denote (values (signature (τ := τ) (Φ := Φ) pe)) (typeModel pe) d) :=
  denote_isPure_proof pe d h

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic
