module

public import Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming.Action.Defs
public import Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming.Category.Defs
public import Silmaril.Logic.Smt.Uflia.SortMaps.Consequence.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming
open CategoryTheory Silmaril.Inst Silmaril.Logic.Institution Uflia.SExpr
variable {E F G : Environment}

theorem mapSentence_id (s : Sentence E) : mapSentence (NameMap.id E) s = s := by
  induction s using Quotient.inductionOn with
  | h a =>
    exact Quotient.sound (Hom.quantifiedSentence_id (A := environmentSignature E) a.sentence)

theorem mapSentence_comp (f : NameMap E F) (g : NameMap F G) (s : Sentence E) :
    mapSentence (f.comp g) s = mapSentence g (mapSentence f s) := by
  induction s using Quotient.inductionOn with
  | h a => exact Quotient.sound (Hom.quantifiedSentence_comp f.abstract g.abstract a.sentence)

/-- Truth comes from the independent named-source evaluator on byte representatives. -/
def Holds {E : Environment} (M : Uflia.Model E.signature) (s : Sentence E) : Prop :=
  Uflia.Quantified.SExpr.Renaming.Presentation.Holds M s

theorem holds_iff_decode {E : Environment} (M : Uflia.Model E.signature) (s : Sentence E) :
    Holds M s ↔ s.decode.Holds M :=
  Uflia.Quantified.SExpr.Renaming.Presentation.holds_iff_decode M s

theorem holds_map {S T : EnvironmentSignature} (f : S ⟶ T)
    (M : Uflia.Model T.environment.signature) (s : Sentence S.environment) :
    Holds M (mapSentence f s) ↔ Holds (Hom.reduct f.abstract M) s := by
  rw [holds_iff_decode, holds_iff_decode, decode_map]
  exact Hom.holds_quantifiedSentence f.abstract M s.decode

/-- The model category keeps every ordinary operation-preserving homomorphism.
Quantified truth transport is the signature-reduct theorem, not a claim about
arbitrary model arrows. -/
def room (S : EnvironmentSignature) : Room.{0,0,1} :=
  ⟨Sentence S.environment, Cat.of (Uflia.Model S.environment.signature), Holds⟩

def corridor {S T : EnvironmentSignature} (f : S ⟶ T) : room S ⟶ room T :=
  ⟨mapSentence f, Hom.reductFunctor f.abstract, holds_map f⟩

def institution : EnvironmentSignature ⥤ Room.{0,0,1} where
  obj := room
  map := corridor
  map_id S := Room.hom_ext (funext mapSentence_id)
    (Hom.model_reductFunctor_id (environmentSignature S.environment))
  map_comp f g := Room.hom_ext (funext (mapSentence_comp f g))
    (Hom.model_reductFunctor_comp f.abstract g.abstract)

def inst : Inst.{0,0,0,0,1} := ⟨EnvironmentSignature, institution⟩

/-- Restriction to environments obtained from checked declaration prefixes. -/
def prefixInstitution : PrefixSignature ⥤ Room.{0,0,1} := prefixFunctor ⋙ institution

def prefixInst : Inst.{0,0,0,0,1} := ⟨PrefixSignature, prefixInstitution⟩

/-- Actual source rewriting and the typed varying-sort action form a natural
satisfaction square, with identity interpretation of the full model category. -/
def toAbstract : Inst.CoHom inst SortMaps.QuantifiedModels.inst where
  Φ := environmentFunctor
  ρ :=
    { app S := ⟨Uflia.Quantified.SExpr.Renaming.Presentation.Sentence.decode, 𝟭 _,
        fun M s => (holds_iff_decode M s).symm⟩
      naturality := by
        intro S T f
        exact Room.hom_ext (funext (decode_map f)) rfl }

theorem toAbstract_modelExpansive (S : EnvironmentSignature) :
    (toAbstract.ρ.app S).ModelExpansive := fun M => ⟨M, rfl⟩

theorem satisfiable_of_map {S T : EnvironmentSignature} (f : S ⟶ T)
    {Γ : Set (Sentence S.environment)}
    (h : (room T).Satisfiable (mapSentence f '' Γ)) : (room S).Satisfiable Γ :=
  (corridor f).satisfiable_of_map h

theorem unsatisfiable_map {S T : EnvironmentSignature} (f : S ⟶ T)
    {Γ : Set (Sentence S.environment)} (h : (room S).Unsatisfiable Γ) :
    (room T).Unsatisfiable (mapSentence f '' Γ) := (corridor f).unsatisfiable_map h

theorem entails_map {S T : EnvironmentSignature} (f : S ⟶ T)
    {Γ : Set (Sentence S.environment)} {φ : Sentence S.environment}
    (h : (room S).Entails Γ φ) : (room T).Entails (mapSentence f '' Γ) (mapSentence f φ) :=
  (corridor f).entails_map h

end Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming
