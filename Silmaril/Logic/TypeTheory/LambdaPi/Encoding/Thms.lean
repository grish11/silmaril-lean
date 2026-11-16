module

public import Silmaril.Logic.TypeTheory.LambdaPi.Encoding.Defs
public import Silmaril.Proofs.Logic.TypeTheory.LambdaPi.Encoding

@[expose] public section

namespace Silmaril.Logic.TypeTheory.LambdaPi

open CategoryTheory Silmaril.Calculi.LambdaCube Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Metatheory
open Silmaril.Proofs.Logic.TypeTheory.LambdaPi

namespace ConstantAssignment

/-- A closed assignment preserves every free-variable budget. -/
theorem preserves_scope (F : ConstantAssignment) {t : Term} {n : ℕ} (h : t.Scoped n) :
    (F.term t).Scoped n := assignment_scoped F t h

/-- Term-valued constant replacement commutes with variable renaming. -/
theorem rename (F : ConstantAssignment) (t : Term) (ρ : ℕ → ℕ) :
    F.term (t.rename ρ) = (F.term t).rename ρ := assignment_rename F t ρ

/-- Term-valued constant replacement commutes with simultaneous substitution. -/
theorem subst (F : ConstantAssignment) (t : Term) (σ : ℕ → Term) :
    F.term (t.subst σ) = (F.term t).subst (fun i => F.term (σ i)) := assignment_subst F t σ

/-- The assignment leaving global constants unchanged. -/
def identity : ConstantAssignment where
  constants := Term.constant
  closed _ := True.intro

/-- Compose assignments by translating the entire first image. -/
def comp (F G : ConstantAssignment) : ConstantAssignment where
  constants c := G.term (F.constants c)
  closed c := G.preserves_scope (F.closed c)

/-- Name maps are the special case whose images are single constants. -/
def ofNames (f : String → String) : ConstantAssignment where
  constants c := Term.constant (f c)
  closed _ := True.intro

@[simp] theorem term_ofNames (f : String → String) (t : Term) :
    (ofNames f).term t = t.mapConstants f := assignment_names _ f (fun _ => rfl) t

@[simp] theorem judgment_ofNames (f : String → String) (J : Judgment) :
    (ofNames f).judgment J = J.mapConstants f := by
  have ht : (ofNames f).term = Term.mapConstants f := funext (term_ofNames f)
  cases J
  simp only [judgment, Judgment.mapConstants, ht]

@[simp] theorem term_identity (t : Term) : identity.term t = t := assignment_identity identity rfl t

@[simp] theorem term_comp (F G : ConstantAssignment) (t : Term) :
    (F.comp G).term t = G.term (F.term t) := assignment_composition F G _ (fun _ => rfl) t

@[simp] theorem judgment_identity (J : Judgment) : identity.judgment J = J := by
  have ht : identity.term = id := funext term_identity
  cases J
  simp [judgment, ht]

@[simp] theorem judgment_comp (F G : ConstantAssignment) (J : Judgment) :
    (F.comp G).judgment J = G.judgment (F.judgment J) := by
  have ht : (F.comp G).term = G.term ∘ F.term := funext (term_comp F G)
  cases J
  simp only [judgment, ht, List.map_map, Function.comp_apply]

end ConstantAssignment

/-- Instantiated β/rewrite conversion is stable under capture-avoiding substitution. -/
theorem Calculus.Conversion.subst {C : Calculus} {t u : Term}
    (h : C.Conversion t u) (σ : ℕ → Term) : C.Conversion (t.subst σ) (u.subst σ) :=
  conversion_subst h σ

/-- An encoding preserves all conversion generators and their compatible closure. -/
theorem Encoding.map_conversion {C D : TypedPresentation} (F : Encoding C D) {t u : Term}
    (h : C.calculus.Conversion t u) : D.calculus.Conversion (F.term t) (F.term u) :=
  encoding_conversion F h

/-- The local declaration and rewrite certificates imply all-rule hypothetical typing preservation. -/
theorem Encoding.map_derives {C D : TypedPresentation} (F : Encoding C D)
    {H : Set Judgment} {J : Judgment} (h : Derives C.calculus H J) :
    Derives D.calculus (F.judgment '' H) (F.judgment J) := encoding_derives F h

@[ext] theorem Encoding.ext {C D : TypedPresentation} {F G : Encoding C D}
    (h : F.constants = G.constants) : F = G := by
  cases F with
  | mk F hd hr =>
    cases G with
    | mk G hd' hr' =>
      cases F
      cases G
      cases h
      rfl

/-- Every typed presentation has an identity encoding, with proved declaration typings. -/
def Encoding.identity (C : TypedPresentation) : Encoding C C where
  toConstantAssignment := .identity
  declared := by
    intro c A hd
    obtain ⟨s, hs⟩ := C.sorted hd
    change Derives C.calculus ∅ ⟨[], Term.constant c, ConstantAssignment.identity.term A⟩
    simpa only [ConstantAssignment.term_identity] using (Derives.constant hd hs)
  rules := by
    intro r hr
    simpa only [ConstantAssignment.term_identity,
      Pseudo.subst_var _ _ (fun _ => rfl)] using
      (Calculus.Conversion.rewrite (C := C.calculus) r hr Pseudo.var)

/-- Composition uses the proved typing and conversion preservation results. -/
def Encoding.comp {C D E : TypedPresentation} (F : Encoding C D) (G : Encoding D E) :
    Encoding C E where
  toConstantAssignment := F.toConstantAssignment.comp G.toConstantAssignment
  declared := by
    intro c A hd
    change Derives E.calculus ∅ ⟨[], G.term (F.constants c),
      (F.toConstantAssignment.comp G.toConstantAssignment).term A⟩
    rw [ConstantAssignment.term_comp]
    simpa only [Set.image_empty, ConstantAssignment.judgment, List.map_nil,
      ConstantAssignment.term_comp] using G.map_derives (F.declared hd)
  rules := by
    intro r hr
    simpa only [ConstantAssignment.term_comp] using G.map_conversion (F.rules r hr)

/-- Typed presentations with term-valued encodings form a category. -/
instance : Category TypedPresentation where
  Hom := Encoding
  id := Encoding.identity
  comp := Encoding.comp
  id_comp F := by
    apply Encoding.ext
    rfl
  comp_id F := by
    apply Encoding.ext
    funext c
    exact ConstantAssignment.term_identity (F.constants c)
  assoc F G H := by
    apply Encoding.ext
    funext c
    exact (ConstantAssignment.term_comp G.toConstantAssignment H.toConstantAssignment (F.constants c)).symm

/-- The concrete inference rules are functorial under term-valued encodings. -/
def encodingsToEntailment : TypedPresentation ⥤ ER where
  obj C := C.calculus.entailment
  map F := ⟨F.judgment, F.map_derives⟩
  map_id _ := by
    apply ER.hom_ext
    funext J
    exact ConstantAssignment.judgment_identity J
  map_comp F G := by
    apply ER.hom_ext
    funext J
    exact ConstantAssignment.judgment_comp F.toConstantAssignment G.toConstantAssignment J

/-- Each checked LF signature supplies the declaration derivations required by the encoding category. -/
def CheckedSignature.presentation (S : CheckedSignature) : TypedPresentation where
  calculus := S.calculus
  sorted := S.checked.declared_sorted

/-- Retain the existing structural translations inside the larger encoding class. -/
def Encoding.ofMorphism {C D : TypedPresentation} (F : Morphism C.calculus D.calculus) :
    Encoding C D where
  toConstantAssignment := .ofNames F.constants
  declared := by
    intro c A hd
    obtain ⟨s, hs⟩ := D.sorted (F.declared hd)
    change Derives D.calculus ∅ ⟨[], Term.constant (F.constants c),
      (ConstantAssignment.ofNames F.constants).term A⟩
    simpa only [ConstantAssignment.term_ofNames] using (Derives.constant (F.declared hd) hs)
  rules := by
    intro r hr
    have hl := Pseudo.subst_var (r.mapConstants F.constants).lhs Pseudo.var (fun _ => rfl)
    have hh := Pseudo.subst_var (r.mapConstants F.constants).rhs Pseudo.var (fun _ => rfl)
    have he := Calculus.Conversion.rewrite (C := D.calculus) (r.mapConstants F.constants)
      (F.rules r hr) Pseudo.var
    rw [hl, hh] at he
    simpa only [RewriteRule.mapConstants, ConstantAssignment.term_ofNames] using he

/-- Ordered checked LF signatures embed functorially into term-valued presentations. -/
def checkedSignaturesToEncodings : CheckedSignature ⥤ TypedPresentation where
  obj := CheckedSignature.presentation
  map F := Encoding.ofMorphism F
  map_id _ := by apply Encoding.ext; rfl
  map_comp _ _ := by apply Encoding.ext; rfl

/-- The structural and term-valued routes give exactly the same entailment translations. -/
theorem checkedSignature_entailment_commutes :
    checkedSignaturesToEncodings ⋙ encodingsToEntailment =
      checkedSignaturesToCalculi ⋙ calculusToEntailment := by
  apply CategoryTheory.Functor.hext
    (F := checkedSignaturesToEncodings ⋙ encodingsToEntailment)
    (G := checkedSignaturesToCalculi ⋙ calculusToEntailment) (fun _ => rfl)
  intro S T F
  apply heq_of_eq
  apply ER.hom_ext
  funext J
  exact ConstantAssignment.judgment_ofNames F.constants J

/-- Term-valued encodings induce the closed-theory institution comorphisms. -/
noncomputable def encodingInstitutions : TypedPresentation ⥤ CoIns.{0,0,0,0,0} :=
  encodingsToEntailment ⋙ Silmaril.Logic.Institution.Syntactic.toInstitutions

/-- The checked-signature institution functor agrees through the larger translation category. -/
theorem checkedSignature_institution_commutes :
    checkedSignaturesToEncodings ⋙ encodingInstitutions = checkedSignatureInstitutions := by
  change (checkedSignaturesToEncodings ⋙ encodingsToEntailment) ⋙
    Silmaril.Logic.Institution.Syntactic.toInstitutions = _
  rw [checkedSignature_entailment_commutes]
  rfl

/-- The same encodings supply Hets logic-translation edges. -/
noncomputable def encodingHets := IndexedCoInst.toLogicGraph encodingInstitutions

end Silmaril.Logic.TypeTheory.LambdaPi
