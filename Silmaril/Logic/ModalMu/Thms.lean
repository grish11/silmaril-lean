module

public import Silmaril.Proofs.Logic.ModalMu.Semantics

@[expose] public section
namespace Silmaril.Logic.ModalMu
open CategoryTheory Silmaril.Logic.Institution

def modelReduct {S T : Signature} (f : S ⟶ T) : Model T ⥤ Model S where
  obj := reduct f
  map h := ⟨congrArg (reduct f) h.down⟩

def institution : Signature ⥤ Room where
  obj S := ⟨Formula S 0, Cat.of (Model S), Sat⟩
  map f := ⟨Formula.map f, modelReduct f, by
    intro M p
    change M.point ∈ (p.map f).denote M emptyEnv ↔
      M.point ∈ p.denote (reduct f M) emptyEnv
    rw [Formula.denote_map]
    rfl⟩
  map_id S := by
    apply Room.hom_ext (funext Formula.map_id)
    rfl
  map_comp f g := by
    apply Room.hom_ext (funext (Formula.map_comp f g))
    rfl

/-- The institution as a bundled `Inst`: its signatures and room functor `institution`, named so
that records and comorphisms can refer to it. -/
def inst := (⟨Signature, institution⟩ : Silmaril.Logic.Institution.Inst)

 theorem sat_dual {S : Signature} (M : Model S) (p : Formula S 0) :
    Sat M p.dual ↔ ¬ Sat M p := by
  have he : (fun i : Fin 0 => (emptyEnv (W := M.World) i)ᶜ) = emptyEnv :=
    funext fun i => i.elim0
  have hd := p.denote_dual M emptyEnv
  rw [he] at hd
  exact Set.ext_iff.mp hd M.point

end Silmaril.Logic.ModalMu
