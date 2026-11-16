module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Functor
public import Silmaril.Logic.Matching.SortMaps.GeneralFixedPoint.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps
open CategoryTheory Silmaril.Logic.Institution

/-- Typed Boolean/general-fixed-point sentences on actual restricted builtin
models with varying scope signatures. The checked raw-source interface is in
`Checker.Institution.Defs`. -/
def nativeRoom (A : Signature) : Room :=
  ⟨Matching.GeneralFixedPoint.Sentence A.scope.signature,
    Cat.of (@Model A.bindings A.scope A.literalPrefix A.literals A.hooks),
    fun M p => Matching.GeneralFixedPoint.Sentence.Satisfies
      (@Model.native A.bindings A.scope A.literalPrefix A.literals A.hooks M) p⟩

/-- Typed satisfaction transport is proved before introducing Room coercions. -/
theorem nativeSatisfaction {A B : Signature} (f : A ⟶ B)
    (M : @Model B.bindings B.scope B.literalPrefix B.literals B.hooks)
    (p : Matching.GeneralFixedPoint.Sentence A.scope.signature) :
    Matching.GeneralFixedPoint.Sentence.Satisfies
      (@Model.native B.bindings B.scope B.literalPrefix B.literals B.hooks M)
      (Matching.SortMaps.Hom.generalSentence f.native p) ↔
    Matching.GeneralFixedPoint.Sentence.Satisfies
      (@Model.native A.bindings A.scope A.literalPrefix A.literals A.hooks (Hom.reduct f M)) p := by
  rw [Hom.reduct_native]
  exact Matching.SortMaps.Hom.generalSatisfaction f.native
    (@Model.native B.bindings B.scope B.literalPrefix B.literals B.hooks M) p

def nativeCorridor {A B : Signature} (f : A ⟶ B) : nativeRoom A ⟶ nativeRoom B :=
  ⟨Matching.SortMaps.Hom.generalSentence f.native, Hom.reductFunctor f,
    fun M p => nativeSatisfaction f M p⟩

def nativeInstitution : Signature ⥤ Room where
  obj := nativeRoom
  map := nativeCorridor
  map_id A := by
    apply Room.hom_ext
    · funext p
      change Matching.SortMaps.Hom.generalSentence (𝟙 A.native) p = p
      exact Matching.SortMaps.Hom.generalSentence_id (A := A.native) p
    · exact Hom.reductFunctor_id A
  map_comp f g := by
    apply Room.hom_ext
    · funext p
      change Matching.SortMaps.Hom.generalSentence (f.native ≫ g.native) p =
        Matching.SortMaps.Hom.generalSentence g.native
          (Matching.SortMaps.Hom.generalSentence f.native p)
      exact Matching.SortMaps.Hom.generalSentence_comp f.native g.native p
    · exact Hom.reductFunctor_comp f g

/-- `nativeInstitution` as a bundled `Inst`, named so that records and comorphisms can refer to it. -/
def nativeInst := (⟨Signature, nativeInstitution⟩ : Silmaril.Logic.Institution.Inst)

end Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps
