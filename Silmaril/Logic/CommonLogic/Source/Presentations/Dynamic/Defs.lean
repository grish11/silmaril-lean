module

public import Silmaril.Logic.CommonLogic.Source.Presentations.Family.Thms

/-! Symbols in each sentence, with one shared global model. The local signature
and spelling table are carried by the sentence itself, not a predeclared index.
The sentence universe is therefore Type 1. ULift on the target sentences is only
universe bookkeeping: the target models and every model arrow are unchanged. -/
@[expose] public section
namespace Silmaril.Logic.CommonLogic.Source.Presentations.Dynamic
open CategoryTheory Silmaril.Logic.Institution

/-- Raise the sentence universe while retaining the exact model category. -/
def liftRoom (R : Room.{0,0,1}) : Room.{1,0,1} :=
  ⟨ULift.{1} R.Sen, R.Mod, fun M p => R.Sat M p.down⟩

def liftCorridor {R T : Room.{0,0,1}} (f : R ⟶ T) : liftRoom R ⟶ liftRoom T where
  sen p := ⟨f.sen p.down⟩
  mod := f.mod
  sat M p := f.sat M p.down

def coreInstitution : Core.Signature ⥤ Room.{1,0,1} where
  obj S := liftRoom (Core.room S)
  map f := liftCorridor (Core.corridor f)
  map_id S := congrArg liftCorridor (Core.institution.map_id S)
  map_comp f g := congrArg liftCorridor (Core.institution.map_comp f g)

def coreInst : Inst.{1,0,1,0,1} := ⟨Core.Signature, coreInstitution⟩

noncomputable def folInstitution : Core.Signature ⥤ Room.{1,0,1} where
  obj S := liftRoom (FiniteListFOL.room S)
  map f := liftCorridor (FiniteListFOL.corridor f)
  map_id S := congrArg liftCorridor (FiniteListFOL.institution.map_id S)
  map_comp f g := congrArg liftCorridor (FiniteListFOL.institution.map_comp f g)

noncomputable def folInst : Inst.{1,0,1,0,1} := ⟨Core.Signature, folInstitution⟩

/-- Each sentence chooses arbitrary local symbol types, valid named declarations,
an actual class-preserving map to global symbols, and an accepted source text. -/
structure Text (S : Core.Signature) where
  vocabulary : Family.Signature
  symbols : vocabulary.core ⟶ S
  text : CLIF.Text vocabulary.names

def translate {S : Core.Signature} (p : Text S) : Core.Sentence S :=
  (CLIF.conjunction p.text.typed).map p.symbols

def mapText {S T : Core.Signature} (f : S ⟶ T) (p : Text S) : Text T where
  vocabulary := p.vocabulary
  symbols := p.symbols ≫ f
  text := p.text

@[simp] theorem mapText_id {S : Core.Signature} (p : Text S) : mapText (𝟙 S) p = p := by
  cases p
  rfl

theorem mapText_comp {S T U : Core.Signature} (f : S ⟶ T) (g : T ⟶ U) (p : Text S) :
    mapText (f ≫ g) p = mapText g (mapText f p) := rfl

theorem translate_map {S T : Core.Signature} (f : S ⟶ T) (p : Text S) :
    translate (mapText f p) = (translate p).map f :=
  Core.Formula.map_comp p.symbols f _

def room (S : Core.Signature) : Room.{1,0,1} :=
  ⟨Text S, Cat.of (Core.Model S), fun M p =>
    (CLIF.room p.vocabulary.names).Sat ((Core.Model.reduct p.symbols).obj M) p.text⟩

/-- Satisfaction is independent raw source evaluation in the local reduct. -/
theorem translate_adequate {S : Core.Signature} (M : Core.Model S) (p : Text S) :
    (translate p).Holds M Fin.elim0 Fin.elim0 ↔ (room S).Sat M p :=
  (Core.Formula.holds_map p.symbols M Fin.elim0 Fin.elim0 _).trans
    ((CLIF.toCore p.vocabulary.names).sat _ p.text)

def corridor {S T : Core.Signature} (f : S ⟶ T) : room S ⟶ room T where
  sen := mapText f
  mod := Core.Model.reduct f
  sat M p := by
    change Core.Model T at M
    change Text S at p
    exact (translate_adequate M (mapText f p)).symm.trans
      ((show (translate (mapText f p)).Holds M Fin.elim0 Fin.elim0 ↔
        (translate p).Holds ((Core.Model.reduct f).obj M) Fin.elim0 Fin.elim0 by
          rw [translate_map]; exact Core.Formula.holds_map _ _ _ _ _).trans
        (translate_adequate _ p))

def institution : Core.Signature ⥤ Room.{1,0,1} where
  obj := room
  map := corridor
  map_id _S := Room.hom_ext (funext mapText_id) rfl
  map_comp f g := Room.hom_ext (funext (mapText_comp f g)) rfl

def inst : Inst.{1,0,1,0,1} := ⟨Core.Signature, institution⟩

def toCore (S : Core.Signature) : room S ⟶ liftRoom (Core.room S) where
  sen p := ⟨translate p⟩
  mod := 𝟭 _
  sat := translate_adequate

noncomputable def toFOL (S : Core.Signature) : room S ⟶ liftRoom (FiniteListFOL.room S) :=
  toCore S ≫ liftCorridor (FiniteListFOL.comparison S)

def comparison : Inst.CoHom inst coreInst where
  Φ := 𝟭 _
  ρ := { app S := by
           change room S ⟶ liftRoom (Core.room S)
           exact toCore S
         naturality := fun {_ _} f => Room.hom_ext
           (funext fun p => congrArg ULift.up (translate_map f p)) rfl }

noncomputable def liftedComparison : Inst.CoHom coreInst folInst where
  Φ := 𝟭 _
  ρ := { app S := by
           change liftRoom (Core.room S) ⟶ liftRoom (FiniteListFOL.room S)
           exact liftCorridor (FiniteListFOL.comparison S)
         naturality := fun {_ _} f =>
           congrArg liftCorridor (FiniteListFOL.comorphism.ρ.naturality f) }

noncomputable def folComparison : Inst.CoHom inst folInst :=
  Inst.CoHom.comp comparison liftedComparison

end Silmaril.Logic.CommonLogic.Source.Presentations.Dynamic
