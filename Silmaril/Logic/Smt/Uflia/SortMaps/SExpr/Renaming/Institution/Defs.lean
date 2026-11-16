module

public import Silmaril.Logic.Smt.Uflia.SortMaps.SExpr.Renaming.Action.Defs
public import Silmaril.Logic.Smt.Uflia.SortMaps.SExpr.Renaming.Category.Defs
public import Silmaril.Logic.Smt.Uflia.SortMaps.Consequence.Thms
public import Silmaril.Logic.Smt.Uflia.SExpr.Surface.Renaming.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Smt.Uflia.SortMaps.SExpr.Renaming
open CategoryTheory Silmaril.Inst Silmaril.Logic.Institution Uflia.SExpr
variable {E F G : Environment}

theorem mapSentence_id (s : Sentence E) : mapSentence (NameMap.id E) s = s := by
  apply (Uflia.SExpr.Renaming.Concrete.Sentence.decode_eq_iff _ _).mp
  rw [decode_map]
  exact Hom.formula_id (A := environmentSignature E) s.decode

theorem mapSentence_comp (f : NameMap E F) (g : NameMap F G) (s : Sentence E) :
    mapSentence (f.comp g) s = mapSentence g (mapSentence f s) := by
  apply (Uflia.SExpr.Renaming.Concrete.Sentence.decode_eq_iff _ _).mp
  rw [decode_map, decode_map, decode_map]
  exact Hom.formula_comp f.abstract g.abstract s.decode

/-- The original direct named-source interpreter defines satisfaction. Checked
prefixes provide the unique-name evidence used by its decoder comparison. -/
def Holds (checked : DeclarationPrefix) (M : Uflia.Model checked.environment.signature)
    (s : Sentence checked.environment) : Prop :=
  Uflia.SExpr.Surface.Renaming.Holds checked M s

theorem holds_iff_decode (checked : DeclarationPrefix)
    (M : Uflia.Model checked.environment.signature) (s : Sentence checked.environment) :
    Holds checked M s ↔ M.Holds s.decode :=
  Uflia.SExpr.Surface.Renaming.holds_iff checked M s

theorem holds_map {S T : PrefixSignature} (f : S ⟶ T)
    (M : Uflia.Model T.prefix.environment.signature)
    (s : Sentence S.prefix.environment) :
    Holds T.prefix M (mapSentence f s) ↔ Holds S.prefix (Hom.reduct f.abstract M) s := by
  rw [holds_iff_decode, holds_iff_decode, decode_map]
  exact Hom.holds_formula f.abstract M s.decode

/-- Each source room keeps all ordinary model homomorphisms. -/
def room (S : PrefixSignature) : Room.{0,0,1} :=
  ⟨Sentence S.prefix.environment, Cat.of (Uflia.Model S.prefix.environment.signature),
    Holds S.prefix⟩

def corridor {S T : PrefixSignature} (f : S ⟶ T) : room S ⟶ room T :=
  ⟨mapSentence f, Hom.reductFunctor f.abstract, holds_map f⟩

def institution : PrefixSignature ⥤ Room.{0,0,1} where
  obj := room
  map := corridor
  map_id S := Room.hom_ext (funext mapSentence_id)
    (Hom.model_reductFunctor_id (environmentSignature S.prefix.environment))
  map_comp f g := Room.hom_ext (funext (mapSentence_comp f g))
    (Hom.model_reductFunctor_comp f.abstract g.abstract)

def inst : Inst.{0,0,0,0,1} := ⟨PrefixSignature, institution⟩

/-- Decoding is natural for actual source renaming and varying-sort reducts. -/
def toAbstract : Inst.CoHom inst SortMaps.inst where
  Φ := prefixAbstractFunctor
  ρ :=
    { app S := ⟨Uflia.SExpr.Renaming.Concrete.Sentence.decode, 𝟭 _,
        fun M s => (holds_iff_decode S.prefix M s).symm⟩
      naturality := by
        intro S T f
        exact Room.hom_ext (funext (decode_map f)) rfl }

theorem toAbstract_modelExpansive (S : PrefixSignature) :
    (toAbstract.ρ.app S).ModelExpansive := fun M => ⟨M, rfl⟩

theorem satisfiable_of_map {S T : PrefixSignature} (f : S ⟶ T)
    {Γ : Set (Sentence S.prefix.environment)}
    (h : (room T).Satisfiable (mapSentence f '' Γ)) : (room S).Satisfiable Γ :=
  (corridor f).satisfiable_of_map h

theorem unsatisfiable_map {S T : PrefixSignature} (f : S ⟶ T)
    {Γ : Set (Sentence S.prefix.environment)} (h : (room S).Unsatisfiable Γ) :
    (room T).Unsatisfiable (mapSentence f '' Γ) := (corridor f).unsatisfiable_map h

theorem entails_map {S T : PrefixSignature} (f : S ⟶ T)
    {Γ : Set (Sentence S.prefix.environment)} {φ : Sentence S.prefix.environment}
    (h : (room S).Entails Γ φ) : (room T).Entails (mapSentence f '' Γ) (mapSentence f φ) :=
  (corridor f).entails_map h

end Silmaril.Logic.Smt.Uflia.SortMaps.SExpr.Renaming
