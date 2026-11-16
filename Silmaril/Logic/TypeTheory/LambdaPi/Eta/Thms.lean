module

public import Silmaril.Logic.TypeTheory.LambdaPi.Eta.Defs
public import Silmaril.Proofs.Logic.TypeTheory.LambdaPi.Eta
public import Silmaril.Proofs.Logic.TypeTheory.LambdaPi.EtaBoundary

@[expose] public section

namespace Silmaril.Logic.TypeTheory.LambdaPi

open CategoryTheory Silmaril.Calculi.LambdaCube
open Silmaril.Proofs.Logic.TypeTheory.LambdaPi

/-- The encoded η schema produces exactly the capture-avoiding function η equation. -/
theorem Calculus.eta (C : Calculus) (A f : Term) :
    C.withEta.Conversion (.lam A (.app (f.rename Nat.succ) (.var 0))) f := eta_step C A f

/-- The optional LF profile has exactly independently specified annotated βη conversion. -/
theorem Calculus.lfBetaEta_conversion_iff (declared : String → Term → Prop) (t u : Term) :
    (Calculus.lfBetaEta declared).Conversion t u ↔ BetaEtaConversion t u :=
  ⟨beta_eta_of_profile declared, profile_of_beta_eta declared⟩

/-- Raw βη identifies identities with arbitrary domain annotations.
This is an untyped equation; it supplies no common typing for the two identities.
-/
theorem BetaEtaConversion.identity_annotations (A B : Term) :
    BetaEtaConversion (.lam A (.var 0)) (.lam B (.var 0)) :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.EtaBoundary.identity_annotations A B

/-- Existing typings are preserved when the η schema is added. -/
theorem Calculus.derives_withEta (C : Calculus) {H : Set Judgment} {J : Judgment}
    (h : Derives C H J) : Derives C.withEta H J := by
  have hj : Judgment.mapConstants id = id := funext judgment_map_id
  simpa only [Calculus.includeEta, hj, Set.image_id, id_eq] using (C.includeEta.map_derives h)

/-- Structural translations extend to η presentations; the η schema has no constants. -/
def Morphism.withEta {C D : Calculus} (F : Morphism C D) : Morphism C.withEta D.withEta where
  constants := F.constants
  declared := F.declared
  rules := by
    intro r hr
    rcases hr with hr | hr
    · exact Set.mem_union_left _ (F.rules r hr)
    · have he := Set.mem_singleton_iff.mp hr
      subst r
      exact Set.mem_union_right _ (by rw [eta_map_rule]; exact Set.mem_singleton _)

/-- Adding η is functorial on the existing category of raw presentations. -/
def etaExtension : Calculus ⥤ Calculus where
  obj := Calculus.withEta
  map := Morphism.withEta
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The original presentation includes naturally into its η extension. -/
def etaInclusion : 𝟭 Calculus ⟶ etaExtension where
  app := Calculus.includeEta
  naturality := by intro X Y f; rfl

/-- Sorted declarations remain sorted under extension by η. -/
def TypedPresentation.withEta (C : TypedPresentation) : TypedPresentation where
  calculus := C.calculus.withEta
  sorted := by
    intro c A hd
    obtain ⟨s, hs⟩ := C.sorted hd
    exact ⟨s, C.calculus.derives_withEta hs⟩

/-- A term-valued encoding also extends: it fixes the constant-free η schema. -/
def Encoding.withEta {C D : TypedPresentation} (F : Encoding C D) :
    Encoding C.withEta D.withEta where
  toConstantAssignment := F.toConstantAssignment
  declared hd := D.calculus.derives_withEta (F.declared hd)
  rules := by
    intro r hr
    rcases hr with hr | hr
    · have he := conversion_map D.calculus.includeEta (F.rules r hr)
      change D.calculus.withEta.Conversion (F.term r.lhs) (F.term r.rhs)
      simpa only [Calculus.includeEta, map_id] using he
    · have he := Set.mem_singleton_iff.mp hr
      subst r
      have h := Calculus.Conversion.rewrite (C := D.calculus.withEta) etaRule
        (Set.mem_union_right _ (Set.mem_singleton _)) Pseudo.var
      change D.calculus.withEta.Conversion etaRule.lhs etaRule.rhs
      simpa only [Pseudo.subst_var _ _ (fun _ => rfl)] using h

/-- η extension is functorial for compound constant implementations as well. -/
def etaEncodingExtension : TypedPresentation ⥤ TypedPresentation where
  obj := TypedPresentation.withEta
  map := Encoding.withEta
  map_id _ := by apply Encoding.ext; rfl
  map_comp _ _ := by apply Encoding.ext; rfl

end Silmaril.Logic.TypeTheory.LambdaPi
