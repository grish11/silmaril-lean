module

public import Silmaril.Logic.Matching.SortMaps.GeneralFixedPoint.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.SortMaps
open CategoryTheory Silmaril.Logic.Institution

/-- Full Boolean/general fixed-point matching over genuinely varying sorts. -/
def generalInstitution : Signature ⥤ Room where
  obj A := ⟨GeneralFixedPoint.Sentence A.symbols, Cat.of (FirstOrder.Model A.symbols),
    GeneralFixedPoint.Sentence.Satisfies⟩
  map f := ⟨Hom.generalSentence f, Hom.reductFunctor f, Hom.generalSatisfaction f⟩
  map_id _ := Room.hom_ext (funext Hom.generalSentence_id) Hom.reductFunctor_id
  map_comp f g := Room.hom_ext (funext (Hom.generalSentence_comp f g))
    (Hom.reductFunctor_comp f g)

/-- `generalInstitution` as a bundled `Inst`, named so that records and comorphisms can refer to it. -/
def generalInst := (⟨Signature, generalInstitution⟩ : Silmaril.Logic.Institution.Inst)

/-- The existing fixed-sort full Boolean pattern action agrees with the new
varying-sort action on every constructor, including complement and μ/ν. -/
theorem fixedSort_generalPattern {S : Type} {A B : SortedSignature S} (f : A ⟶ B)
    {r k : Nat} {P : Fin r → S} {Γ : Fin k → S} {s : S}
    (p : GeneralFixedPoint.Pattern A P Γ s) :
    Hom.generalPattern ((fixedSortSignatures S).map f) p = GeneralFixedPoint.Pattern.map f p := by
  induction p with
  | base p => exact congrArg GeneralFixedPoint.Pattern.base (fixedSort_pattern f p)
  | setvar => rfl
  | app op _ ih => exact congrArg (GeneralFixedPoint.Pattern.app _) (funext ih)
  | neg _ ih => exact congrArg GeneralFixedPoint.Pattern.neg ih
  | conj _ _ hp hq => exact congrArg₂ GeneralFixedPoint.Pattern.conj hp hq
  | ex bound p hp =>
      change GeneralFixedPoint.Pattern.ex bound _ = GeneralFixedPoint.Pattern.ex bound _
      exact congrArg (GeneralFixedPoint.Pattern.ex bound) hp
  | mu _ ih => exact congrArg GeneralFixedPoint.Pattern.mu ih
  | nu _ ih => exact congrArg GeneralFixedPoint.Pattern.nu ih

/-- Actual natural graph arrow from the existing fixed-sort institution. Both
models and sentences retain their existing meaning; the admission proof is
transported by the independently proved pattern-action equality. -/
def fixedSortGeneral (S : Type) : GeneralFixedPoint.institution S ⟶
    fixedSortSignatures S ⋙ generalInstitution where
  app A := ⟨id, 𝟭 _, fun _ _ => Iff.rfl⟩
  naturality := by
    intro A B f
    apply Room.hom_ext
    · funext p
      change GeneralFixedPoint.Sentence.map f p =
        Hom.generalSentence ((fixedSortSignatures S).map f) p
      cases p
      simp only [GeneralFixedPoint.Sentence.map, Hom.generalSentence,
        fixedSort_generalPattern]
      rfl
    · rfl

end Silmaril.Logic.Matching.SortMaps
