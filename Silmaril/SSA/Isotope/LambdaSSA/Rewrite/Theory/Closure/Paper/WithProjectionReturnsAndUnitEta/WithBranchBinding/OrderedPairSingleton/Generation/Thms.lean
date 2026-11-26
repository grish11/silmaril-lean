module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton.Generation.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton.Operations.Comparison.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Generation.Domain.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OrderedPairRawGeneration

/-! # Raw and guarded generation give the same generated domain -/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton.Generation

open Silmaril CategoryTheory
open Operations (operationIso)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

local notation "Join" => WithPairReturns.JoinedStep (τ := τ) (Φ := Φ) pe
local notation "H" => RawHom (Φ := Φ) pe
local notation "G" => Paper.Extension.Singleton.ofType (Φ := Φ) Join
local notation "GuardedGenerated" => Paper.Extension.Singleton.Generation.Generated Join

local notation "Cmp" => operationIso (τ := τ) (Φ := Φ) pe
local notation "E" => Operations.OperationIso.homEquiv (Cmp)

theorem normalize_generated {A B : τ} {f : H A B} (hf : Generated pe f) :
    GuardedGenerated (E A B f) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OrderedPairRawGeneration.normalize_generated pe hf

theorem toRaw_generated {A B : τ} {g : G A ⟶ G B} (hg : GuardedGenerated g) :
    Generated pe ((E A B).symm g) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OrderedPairRawGeneration.toRaw_generated pe hg

/-- A raw arrow is generated exactly when its normalization is generated in the guarded join. -/
theorem generated_iff_normalize {A B : τ} (f : H A B) :
    Generated pe f ↔ GuardedGenerated (normalizeHom pe f) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OrderedPairRawGeneration.generated_iff_normalize pe f

local notation "RawDomain" => Category (τ := τ) (Φ := Φ) pe
local notation "GuardedDomain" => Paper.Extension.Singleton.Generation.Domain.Category Join

def normalizeGenerated : RawDomain ⥤ GuardedDomain where
  obj X := ⟨(normalizeFunctor pe).obj X.obj⟩
  map f := ⟨normalizeHom pe f.1, normalize_generated pe f.2⟩
  map_id X := WideSubcategory.hom_ext _ (normalize_identity pe (A := X.obj.as))
  map_comp f g := WideSubcategory.hom_ext _ (normalize_compose pe f.1 g.1)

noncomputable def toRawGenerated : GuardedDomain ⥤ RawDomain where
  obj X := ⟨(toRawFunctor pe).obj X.obj⟩
  map f := ⟨toRawHom pe f.1, toRaw_generated pe f.2⟩
  map_id X := WideSubcategory.hom_ext _ ((toRawFunctor pe).map_id X.obj)
  map_comp f g := WideSubcategory.hom_ext _ ((toRawFunctor pe).map_comp f.1 g.1)

/-- The two generated wide subcategories are strictly isomorphic. -/
noncomputable def categoryIso : Cat.of RawDomain ≅ Cat.of GuardedDomain where
  hom := (normalizeGenerated pe).toCatHom
  inv := (toRawGenerated pe).toCatHom
  hom_inv_id := by
    apply Cat.ext
    change normalizeGenerated pe ⋙ toRawGenerated pe = 𝟭 _
    refine Functor.hext (fun _ => rfl) (fun X Y f => ?_)
    exact heq_of_eq (WideSubcategory.hom_ext _ ((E X.obj.as Y.obj.as).symm_apply_apply f.1))
  inv_hom_id := by
    apply Cat.ext
    change toRawGenerated pe ⋙ normalizeGenerated pe = 𝟭 _
    refine Functor.hext (fun _ => rfl) (fun X Y f => ?_)
    exact heq_of_eq (WideSubcategory.hom_ext _ (normalize_toRawHom pe f.1))

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton.Generation
