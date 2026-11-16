module

public import Silmaril.Logic.CommonLogic.Source.Presentations.Family.Thms

/-! A packaged sentence carries a local named vocabulary. Its semantic symbols
map into one shared global vocabulary. All sentences of a theory are interpreted
in the same global model; the models are not a product of unrelated local models.
The arbitrary index type stays fixed along presentation arrows. -/
@[expose] public section
namespace Silmaril.Logic.CommonLogic.Source.Presentations.Packaged
open CategoryTheory Silmaril.Logic.Institution

structure Signature (I : Type) where
  global : Core.Signature
  vocabulary : I → Family.Signature
  symbols : (i : I) → (vocabulary i).core ⟶ global

/-- Every package retains the accepted bytes, parser equation and computed local
elaboration, together with the index of its local vocabulary. -/
def Text {I : Type} (A : Signature I) := (i : I) × CLIF.Text (A.vocabulary i).names

def room {I : Type} (A : Signature I) : Room.{0,0,1} :=
  ⟨Text A, Cat.of (Core.Model A.global), fun M p =>
    (CLIF.room (A.vocabulary p.1).names).Sat ((Core.Model.reduct (A.symbols p.1)).obj M) p.2⟩

/-- The actual local-to-global symbol map relates independent raw source
satisfaction to the full global Core language. -/
def toCore {I : Type} (A : Signature I) : room A ⟶ Core.room A.global where
  sen p := (CLIF.conjunction p.2.typed).map (A.symbols p.1)
  mod := 𝟭 _
  sat M p := by
    exact (Core.Formula.holds_map (A.symbols p.1) M Fin.elim0 Fin.elim0
      (CLIF.conjunction p.2.typed)).trans ((CLIF.toCore (A.vocabulary p.1).names).sat _ p.2)

noncomputable def toFOL {I : Type} (A : Signature I) : room A ⟶ FiniteListFOL.room A.global :=
  toCore A ≫ FiniteListFOL.comparison A.global

structure Signature.Hom {I : Type} (A B : Signature I) where
  global : A.global ⟶ B.global
  vocabulary : (i : I) → A.vocabulary i ⟶ B.vocabulary i
  commutes : ∀ i, (vocabulary i).symbols ≫ B.symbols i = A.symbols i ≫ global

@[ext] theorem Signature.Hom.ext {I : Type} {A B : Signature I}
    (f g : Signature.Hom A B) (global : f.global = g.global)
    (vocabulary : f.vocabulary = g.vocabulary) : f = g := by
  cases f
  cases g
  cases global
  cases vocabulary
  rfl

instance {I : Type} : Category (Signature I) where
  Hom := Signature.Hom
  id A := ⟨𝟙 _, fun i => 𝟙 _, fun i => rfl⟩
  comp f g := ⟨f.global ≫ g.global, fun i => f.vocabulary i ≫ g.vocabulary i, by
    intro i
    change ((f.vocabulary i).symbols ≫ (g.vocabulary i).symbols) ≫ _ = _
    rw [Category.assoc, g.commutes, ← Category.assoc, f.commutes, Category.assoc]⟩
  id_comp f := Signature.Hom.ext _ _ rfl (by funext i; exact Category.id_comp _)
  comp_id f := Signature.Hom.ext _ _ rfl (by funext i; exact Category.comp_id _)
  assoc f g h := Signature.Hom.ext _ _ rfl (by funext i; exact Category.assoc _ _ _)

def forget (I : Type) : Signature I ⥤ Core.Signature where
  obj A := A.global
  map f := f.global
  map_id _ := rfl
  map_comp _ _ := rfl

def mapText {I : Type} {A B : Signature I} (f : A ⟶ B) (p : Text A) : Text B :=
  ⟨p.1, Family.mapText (f.vocabulary p.1) p.2⟩

theorem translate_map {I : Type} {A B : Signature I} (f : A ⟶ B) (p : Text A) :
    (toCore B).sen (mapText f p) = ((toCore A).sen p).map f.global := by
  change (CLIF.conjunction (p.2.typed.map (Core.Formula.map (f.vocabulary p.1).symbols))).map
      (B.symbols p.1) = ((CLIF.conjunction p.2.typed).map (A.symbols p.1)).map f.global
  rw [← Family.conjunction_map, ← Core.Formula.map_comp, f.commutes, Core.Formula.map_comp]

def corridor {I : Type} {A B : Signature I} (f : A ⟶ B) : room A ⟶ room B where
  sen := mapText f
  mod := Core.Model.reduct f.global
  sat M p := by
    change Core.Model B.global at M
    change Text A at p
    exact ((toCore B).sat M (mapText f p)).symm.trans
      ((show ((toCore B).sen (mapText f p)).Holds M Fin.elim0 Fin.elim0 ↔
        ((toCore A).sen p).Holds ((Core.Model.reduct f.global).obj M) Fin.elim0 Fin.elim0 by
          rw [translate_map]; exact Core.Formula.holds_map _ _ _ _ _).trans
        ((toCore A).sat _ p))

def institution (I : Type) : Signature I ⥤ Room.{0,0,1} where
  obj := room
  map := corridor
  map_id A := Room.hom_ext (funext fun p => by
    cases p with
    | mk i text => exact congrArg (Sigma.mk i) (Family.mapText_id _ text)) rfl
  map_comp f g := Room.hom_ext (funext fun p => by
    cases p with
    | mk i text => exact congrArg (Sigma.mk i) (Family.mapText_comp _ _ text)) rfl

def inst (I : Type) : Inst.{1,0,0,0,1} := ⟨Signature I, institution I⟩

def comparison (I : Type) : Inst.CoHom (inst I) Core.inst where
  Φ := forget I
  ρ := { app := toCore
         naturality := fun {_ _} f => Room.hom_ext (funext (translate_map f)) rfl }

noncomputable def folComparison (I : Type) : Inst.CoHom (inst I) FiniteListFOL.inst :=
  Inst.CoHom.comp (comparison I) FiniteListFOL.comorphism

end Silmaril.Logic.CommonLogic.Source.Presentations.Packaged
