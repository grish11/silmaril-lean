module

public import Silmaril.Logic.Algebraic.OrderSorted.Defs
public import Silmaril.Logic.Institution.Hets.Heterogeneous

@[expose] public section
namespace Silmaril.Logic.Algebraic.OrderSorted
open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Examples

variable {A B C : Signature}

private theorem hom_hext {M M' N N' : Model A} (hM : M = M') (hN : N = N')
    (f : M ⟶ N) (g : M' ⟶ N') (h : HEq f.map g.map) : HEq f g := by
  cases hM; cases hN
  cases f; cases g
  cases eq_of_heq h
  rfl

theorem reduct_id (M : Model A) : reduct (𝟙 A) M = M := by
  apply Model.ext
  change (EQ.Algebra.reduct (compileMap (𝟙 A))).obj M.algebra = M.algebra
  rw [compileMap_id]
  rfl

theorem reduct_comp (f : A ⟶ B) (g : B ⟶ C) (M : Model C) :
    reduct (f ≫ g) M = reduct f (reduct g M) := by
  apply Model.ext
  change (EQ.Algebra.reduct (compileMap (f ≫ g))).obj M.algebra = _
  rw [compileMap_comp]
  rfl

theorem reductFunctor_id : reductFunctor (𝟙 A) = 𝟭 (Model A) := by
  apply Functor.hext reduct_id
  intro M N f
  apply hom_hext (reduct_id M) (reduct_id N)
  rfl

theorem reductFunctor_comp (f : A ⟶ B) (g : B ⟶ C) :
    reductFunctor (f ≫ g) = reductFunctor g ⋙ reductFunctor f := by
  apply Functor.hext (reduct_comp f g)
  intro M N h
  apply hom_hext (reduct_comp f g M) (reduct_comp f g N)
  rfl

def sentenceMap (f : A ⟶ B) : Sentence A → Sentence B := EQ.Equation.map (compileMap f)

theorem sentenceMap_id (e : Sentence A) : sentenceMap (𝟙 A) e = e := by
  change e.map (compileMap (𝟙 A)) = e
  rw [compileMap_id, EQ.Equation.map_id]

theorem sentenceMap_comp (f : A ⟶ B) (g : B ⟶ C) (e : Sentence A) :
    sentenceMap (f ≫ g) e = sentenceMap g (sentenceMap f e) := by
  change e.map (compileMap (f ≫ g)) = _
  rw [compileMap_comp, EQ.Equation.map_comp]
  rfl

def Satisfies (M : Model A) (e : Sentence A) : Prop := e.Holds M.algebra

theorem satisfaction (f : A ⟶ B) (M : Model B) (e : Sentence A) :
    Satisfies M (sentenceMap f e) ↔ Satisfies (reduct f M) e :=
  EQ.Equation.holds_map (compileMap f) M.algebra e

/-- Coercion-aware equations are interpreted in actual coherent EQ algebras. -/
def institution : Signature ⥤ Room.{0,0,1} where
  obj A := ⟨Sentence A, Cat.of (Model A), Satisfies⟩
  map f := ⟨sentenceMap f, reductFunctor f, satisfaction f⟩
  map_id _ := Room.hom_ext (funext sentenceMap_id) reductFunctor_id
  map_comp f g := Room.hom_ext (funext (sentenceMap_comp f g)) (reductFunctor_comp f g)

def inst : Inst := ⟨Signature, institution⟩

/-- The source's explicit-inclusion presentation has an actual public EQ target.
This forgets the coherence obligations; it does not assert the Reduction Theorem. -/
def underlying (A : Signature) : Model A ⥤ EQ.Algebra (compiled A) where
  obj M := M.algebra
  map h := h

def toEquationalNat : compiledSignatures ⋙ EQ.institution ⟶ institution where
  app A := ⟨id, underlying A, fun _ _ => Iff.rfl⟩
  naturality := by intro A B f; apply Room.hom_ext <;> rfl

/-- Morphism direction: compiled EQ sentences enter the coercion institution,
while coercion models forget to EQ models. -/
def toEquational : Inst.Hom inst EQ.inst := ⟨compiledSignatures, toEquationalNat⟩

/-- The discrete sort order is equality, including on empty sort sets. -/
def discrete (A : EQ.Signature) : Signature where
  base := A
  order := {
    le := Eq
    le_refl := fun _ => rfl
    le_trans := fun _ _ _ h k => h.trans k
    le_antisymm := fun _ _ h _ => h }

def discreteMap {A B : EQ.Signature} (f : A ⟶ B) : discrete A ⟶ discrete B :=
  ⟨f, fun _ _ h => congrArg f.sorts h⟩

def discreteSignatures : EQ.Signature ⥤ Signature where
  obj := discrete
  map := discreteMap
  map_id _ := Signature.Hom.ext _ _ rfl
  map_comp _ _ := Signature.Hom.ext _ _ rfl

def baseInclusion (A : EQ.Signature) : A ⟶ compiled (discrete A) :=
  ⟨id, fun o => .base o⟩

/-- Every actual EQ algebra expands; diagonal inclusions are equality casts. -/
def expand {A : EQ.Signature} (M : EQ.Algebra A) : Model (discrete A) where
  algebra := {
    carrier := M.carrier
    op := fun o args => match o with
      | .base o => M.op o args
      | .inclusion _ _ h => h ▸ args 0 }
  coherent := {
    identity := fun _ _ => rfl
    injective := fun h => by cases h; exact fun _ _ h => h
    composition := fun h k _ => by cases h; cases k; rfl }

def forgetDiscrete (A : EQ.Signature) : Model (discrete A) ⥤ EQ.Algebra A :=
  underlying (discrete A) ⋙ EQ.Algebra.reduct (baseInclusion A)

theorem forget_expand {A : EQ.Signature} (M : EQ.Algebra A) :
    (forgetDiscrete A).obj (expand M) = M := rfl

theorem baseInclusion_naturality {A B : EQ.Signature} (f : A ⟶ B) (e : EQ.Equation A) :
    (e.map f).map (baseInclusion B) =
      (e.map (baseInclusion A)).map (compileMap (discreteMap f)) := by
  rw [← EQ.Equation.map_comp, ← EQ.Equation.map_comp]
  rfl

/-- Natural in arbitrary public EQ signature maps, including noninjective sort maps. -/
def fromEquationalNat : EQ.institution ⟶ discreteSignatures ⋙ institution where
  app A := ⟨EQ.Equation.map (baseInclusion A), forgetDiscrete A,
    fun M e => EQ.Equation.holds_map (baseInclusion A) M.algebra e⟩
  naturality := by
    intro A B f
    apply Room.hom_ext
    · exact funext (baseInclusion_naturality f)
    · rfl

def fromEquational : Inst.CoHom EQ.inst inst := ⟨discreteSignatures, fromEquationalNat⟩

theorem fromEquational_modelExpansive : fromEquational.ModelExpansive :=
  fun _ M => ⟨expand M, forget_expand M⟩

theorem fromEquational_entails_iff (A : EQ.Signature) (H : Set (EQ.Equation A))
    (e : EQ.Equation A) :
    (EQ.institution.obj A).Entails H e ↔
      (institution.obj (discrete A)).Entails (EQ.Equation.map (baseInclusion A) '' H)
        (e.map (baseInclusion A)) :=
  fromEquational.entails_iff fromEquational_modelExpansive A H e

end Silmaril.Logic.Algebraic.OrderSorted
