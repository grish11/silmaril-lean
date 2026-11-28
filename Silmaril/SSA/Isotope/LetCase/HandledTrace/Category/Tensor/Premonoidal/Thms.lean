module

public import Silmaril.SSA.Isotope.LetCase.HandledTrace.Category.Tensor.Premonoidal.Defs
import Silmaril.Proofs.SSA.Isotope.LetCase.HandledTrace.Category.Tensor.Premonoidal.Purity
import Silmaril.Proofs.SSA.Isotope.LetCase.HandledTrace.Category.Tensor.Premonoidal.Laws

@[expose] public section

namespace Silmaril.Isotope.LetCase.HandledTrace

open CategoryTheory LocallyNameless Silmaril.Isotope.Semantics Silmaril.Elgot.ITree
open Silmaril.Isotope.Refinement.Models (OrderedPremonoidal)

universe u v e s w

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {D : τ → Type (e + 1)} [ProductModel D] [UnitModel D] [CoproductModel D] [EmptyModel D]
  {Events : Type e → Type e} {State : Type s}
  {M : InstructionModel D Φ (Tree Events)} {policy : Handler State Events}

namespace Program

variable {A B C F : τ}

/-- A native pure term is a pure value map when the model implements bottom
effect instructions by pure functions. -/
theorem pureRun_of_pure {ε : Type w} [HasEff Φ ε] [Bot ε] {p : Program Φ A B}
    (compatible : M.RespectsPure (ε := ε)) (written : Pure (⊥ : ε) p.1) :
    p.HasPureRun M :=
  PremonoidalProofs.pureRun_of_pure compatible written

/-- The two native execution orders have the same tree when the left program
is a pure value map. The other program runs on exactly the same input. -/
theorem run_leftTensor_eq_rightTensor_of_left_pure {p : Program Φ A B} (q : Program Φ C F)
    (hp : p.HasPureRun M) (input : D (product A C)) :
    (p.leftTensor q).run M input = (p.rightTensor q).run M input :=
  PremonoidalProofs.run_eq_left_pure q hp input

/-- The corresponding tree equality for a pure value map on the right. -/
theorem run_leftTensor_eq_rightTensor_of_right_pure (p : Program Φ A B) {q : Program Φ C F}
    (hq : q.HasPureRun M) (input : D (product A C)) :
    (p.leftTensor q).run M input = (p.rightTensor q).run M input :=
  PremonoidalProofs.run_eq_right_pure p hq input

end Program

namespace Arrow

variable {A B : Interface M policy}

/-- A representative that returns a pure value function is central against
every native arrow in either position. -/
theorem isCentral_of_pureRun {p : Program Φ A.ty B.ty} (hp : p.HasPureRun M) :
    @PremonoidalCategory.IsCentral _ _ (tensorStruct (M := M) (policy := policy))
      A B (ofProgram p) :=
  PremonoidalProofs.isCentral_of_pureRun hp

/-- Centrality for an arrow given by a native pure term in a compatible model. -/
theorem isCentral_of_pure {ε : Type w} [HasEff Φ ε] [Bot ε] {p : Program Φ A.ty B.ty}
    (compatible : M.RespectsPure (ε := ε)) (written : Pure (⊥ : ε) p.1) :
    @PremonoidalCategory.IsCentral _ _ (tensorStruct (M := M) (policy := policy))
      A B (ofProgram p) :=
  isCentral_of_pureRun (Program.pureRun_of_pure compatible written)

end Arrow

/-- The native handled-trace program category has the existing premonoidal
structure, with the two fixed actions and central pure structural maps. -/
instance premonoidal : PremonoidalCategory (Interface M policy) where
  toMonoidalCategoryStruct := tensorStruct
  tensorHom_def _ _ := rfl
  whiskerLeft_id K A := (tensorLeft K).map_id A
  whiskerLeft_comp K {_ _ _} f g := (tensorLeft K).map_comp f g
  id_whiskerRight A K := (tensorRight K).map_id A
  comp_whiskerRight f g K := (tensorRight K).map_comp f g
  associator_central A B C := by exact Arrow.isCentral_of_pureRun (PremonoidalProofs.assoc_pure A.ty B.ty C.ty)
  leftUnitor_central A := by exact Arrow.isCentral_of_pureRun (PremonoidalProofs.snd_pure unit A.ty)
  rightUnitor_central A := by exact Arrow.isCentral_of_pureRun (PremonoidalProofs.fst_pure A.ty unit)
  associator_naturality_left := Arrow.associator_natural_first
  associator_naturality_middle := Arrow.associator_natural_middle
  associator_naturality_right := Arrow.associator_natural_last
  leftUnitor_naturality f := (tensorLeftUnitIso (M := M) (policy := policy)).hom.naturality f
  rightUnitor_naturality f := (tensorRightUnitIso (M := M) (policy := policy)).hom.naturality f
  pentagon A B C F := by exact Quotient.sound (PremonoidalProofs.pentagon A.ty B.ty C.ty F.ty)
  triangle A B := by exact Quotient.sound (PremonoidalProofs.triangle A.ty B.ty)

/-- The premonoidal structure uses the monotone whiskerings already proved on
the handled-trace hom posets. -/
instance : OrderedPremonoidal (Interface M policy) where
  toOrderedCategory := inferInstance
  whiskerLeft_mono K {_ _ f g} h := by
    change Arrow.whiskerLeft K f ≤ Arrow.whiskerLeft K g
    exact Arrow.whiskerLeft_mono K h
  whiskerRight_mono {_ _ f g} K h := by
    change Arrow.whiskerRight f K ≤ Arrow.whiskerRight g K
    exact Arrow.whiskerRight_mono K h

end Silmaril.Isotope.LetCase.HandledTrace
