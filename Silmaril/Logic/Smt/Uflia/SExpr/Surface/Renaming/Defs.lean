module

public import Silmaril.Logic.Smt.Uflia.SExpr.Surface.Institution.Thms
public import Silmaril.Logic.Smt.Uflia.SExpr.Renaming.Concrete.Institution.Thms

@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.SExpr.Surface.Renaming
open CategoryTheory Silmaril.Inst Silmaril.Logic.Institution
open SExpr.Renaming

/-- A finite interpretation is expanded only to supply the independent source
relation with a coherent typed-name interpretation. No decoder truth occurs here. -/
noncomputable def RepresentativeHolds {E : Environment} (M : Uflia.Model E.signature)
    (a : Concrete.Accepted E) : Prop :=
  Surface.Holds E (Packaged.expand E M) a.expression

/-- Checked injective names make expansion recover the exact finite model. -/
theorem representative_holds_iff {E : Environment} (hE : Packaged.NamesInjective E)
    (M : Uflia.Model E.signature) (a : Concrete.Accepted E) :
    RepresentativeHolds M a ↔ M.Holds a.formula := by
  unfold RepresentativeHolds
  rw [holds_iff_decodeFormula _ _ _ a.decoded, Packaged.expand_reduct E hE M]

/-- Independent source truth is natural under executable representative
normalization for every name map between injectively named raw environments. -/
theorem representative_holds_map {E F : Environment}
    (hE : Packaged.NamesInjective E) (hF : Packaged.NamesInjective F)
    (f : NameMap E F) (M : Uflia.Model F.signature) (a : Concrete.Accepted E) :
    RepresentativeHolds M (a.map f) ↔
      RepresentativeHolds (Uflia.Model.reduct f.abstract M) a := by
  rw [representative_holds_iff hF, representative_holds_iff hE]
  exact Uflia.Model.holds_map f.abstract M a.formula

/-- Direct truth descends to the existing accepted-byte quotient. Its definition
uses the source relation on representatives, with decoding used only to prove descent. -/
noncomputable def Holds (checked : DeclarationPrefix)
    (M : Uflia.Model checked.environment.signature)
    (s : Concrete.Sentence checked.environment) : Prop :=
  Quotient.lift (RepresentativeHolds M) (by
    intro a b h
    apply propext
    rw [representative_holds_iff (Packaged.checked_namesInjective checked),
      representative_holds_iff (Packaged.checked_namesInjective checked), h]) s

/-- Exact comparison with the decoder presentation, not its definition. -/
theorem holds_iff (checked : DeclarationPrefix)
    (M : Uflia.Model checked.environment.signature)
    (s : Concrete.Sentence checked.environment) :
    Holds checked M s ↔ Concrete.Holds M s := by
  refine Quotient.inductionOn s ?_
  intro a
  exact representative_holds_iff (Packaged.checked_namesInjective checked) M a

/-- Genuine arbitrary name maps, including symbol identification, preserve
independent source satisfaction against the actual finite-model reduct. -/
theorem holds_map {S T : PrefixSignature} (f : S ⟶ T)
    (M : Uflia.Model T.prefix.environment.signature)
    (s : Concrete.Sentence S.prefix.environment) :
    Holds T.prefix M (Concrete.Sentence.map f s) ↔
      Holds S.prefix (Uflia.Model.reduct f.abstract M) s := by
  rw [holds_iff, holds_iff]
  exact Concrete.holds_map f M s

/-- Direct source semantics over every coherent name-map arrow of checked prefixes.
Models are finite interpretations; their reduct is the existing abstract reduct. -/
noncomputable def plain : Plain PrefixSignature where
  Sen S := Concrete.Sentence S.prefix.environment
  map f s := Concrete.Sentence.map f s
  map_id _ := Concrete.Sentence.map_id
  map_comp := Concrete.Sentence.map_comp
  Mod S := Uflia.Model S.prefix.environment.signature
  reduct f M := Uflia.Model.reduct f.abstract M
  reduct_id _ := Uflia.Model.reduct_id
  reduct_comp f g M := Uflia.Model.reduct_comp f.abstract g.abstract M
  Sat {S} M s := Holds S.prefix M s
  sat_map := holds_map

noncomputable abbrev institution := plain.toInst
noncomputable abbrev room (checked : DeclarationPrefix) := plain.room (⟨checked⟩ : PrefixSignature)

/-- Identity comparison to the existing byte-quotient institution preserves every
signature arrow, representative quotient sentence, and finite model. -/
noncomputable def comparison : Comorphism institution Concrete.declarationInstitution :=
  Comorphism.ofPlain (𝟭 _) (fun _ => id) (fun _ => id)
    (fun S M s => (holds_iff S.prefix M s).symm)
    (fun _ _ => rfl) (fun _ _ => rfl)

/-- The exact comparison also exists in the reverse direction. -/
noncomputable def comparisonReverse : Comorphism Concrete.declarationInstitution institution :=
  Comorphism.ofPlain (𝟭 _) (fun _ => id) (fun _ => id)
    (fun S M s => holds_iff S.prefix M s)
    (fun _ _ => rfl) (fun _ _ => rfl)

/-- Direct accepted bytes decode naturally to the abstract UF/LIA institution. -/
noncomputable def decodeComorphism :
    Comorphism institution (Uflia.institution String) :=
  Comorphism.ofPlain prefixAbstractFunctor (fun _ => Concrete.Sentence.decode) (fun _ => id)
    (fun S M s => (holds_iff S.prefix M s).symm)
    (fun f s => Concrete.Sentence.decode_map f s)
    (fun _ _ => rfl)

end Silmaril.Logic.Smt.Uflia.SExpr.Surface.Renaming
