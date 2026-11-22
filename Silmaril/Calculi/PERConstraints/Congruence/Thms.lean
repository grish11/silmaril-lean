module

public import Silmaril.Calculi.PERConstraints.Congruence.Defs
public import Silmaril.Calculi.PERConstraints.Thms

@[expose] public section
namespace Silmaril.Calculi.PERConstraints.Congruence

open CategoryTheory Silmaril.Logic.Institution

@[simp] theorem reduct_val {source target : Signature} (rename : source ⟶ target) (model : Model target) :
    (reduct rename model).val = PERConstraints.reduct (forget.map rename) model.val := rfl

@[simp] theorem reduct_id {signature : Signature} (model : Model signature) :
    reduct (𝟙 signature) model = model := rfl

theorem reduct_comp {source middle target : Signature} (first : source ⟶ middle) (second : middle ⟶ target)
    (model : Model target) : reduct (first ≫ second) model = reduct first (reduct second model) := rfl

theorem satisfaction {source target : Signature} (rename : source ⟶ target)
    (model : Model target) (sentence : CNF source.carrier.Term) :
    CNF.Holds model.val (CNF.map rename.term sentence) ↔ CNF.Holds (reduct rename model).val sentence :=
  PERConstraints.satisfaction (forget.map rename) model.val sentence

def corridor {source target : Signature} (rename : source ⟶ target) : room source ⟶ room target :=
  ⟨CNF.map rename.term, Discrete.functor fun model => Discrete.mk (reduct rename model),
    fun model sentence => satisfaction rename model.as sentence⟩

theorem corridor_id (signature : Signature) : corridor (𝟙 signature) = 𝟙 (room signature) := by
  apply Room.hom_ext (funext CNF.map_id)
  exact Discrete.functor_ext (fun _ => rfl)

theorem corridor_comp {source middle target : Signature} (first : source ⟶ middle) (second : middle ⟶ target) :
    corridor (first ≫ second) = corridor first ≫ corridor second := by
  apply Room.hom_ext (funext (CNF.map_comp first.term second.term))
  exact Discrete.functor_ext (fun _ => rfl)

/-- The original CNF semantics on constructor-closed models. -/
def institution : Signature ⥤ Room.{0,0,0} where
  obj := room
  map := corridor
  map_id := corridor_id
  map_comp := corridor_comp

def bundled : Inst := ⟨Signature, institution⟩

def forgetCorridor (signature : Signature) : PERConstraints.room signature.carrier ⟶ room signature :=
  ⟨id, Discrete.functor fun model => Discrete.mk model.val, fun _ _ => Iff.rfl⟩

/-- Forgetting closure leaves models, satisfaction and reducts unchanged on
underlying PERs. The comparison does not assert that all PERs are closed. -/
def forgetModels : Inst.Hom bundled PERConstraints.bundled where
  Φ := forget
  η :=
    { app := forgetCorridor
      naturality _ _ rename := by
        apply Room.hom_ext (f := PERConstraints.corridor (forget.map rename) ≫ forgetCorridor _) rfl
        exact Discrete.functor_ext (fun _ => rfl) }

end Silmaril.Calculi.PERConstraints.Congruence
