module

public import Silmaril.Logic.BrookesSC.Defs
import Silmaril.Proofs.Logic.BrookesSC.Laws

public section

namespace Silmaril.Logic.BrookesSC

open CategoryTheory Silmaril.Logic.Institution

universe u v

variable {W : World.{u}} {S T U : Signature W} {D : Target.{u,v} W} {A : Type u}

@[simp] theorem Program.translate_id (p : Program S A) : p.translate (𝟙 S) = p :=
  Proofs.Logic.BrookesSC.program_translate_id p

@[simp] theorem Program.translate_comp (f : S ⟶ T) (g : T ⟶ U) (p : Program S A) :
    p.translate (f ≫ g) = (p.translate f).translate g :=
  Proofs.Logic.BrookesSC.program_translate_comp f g p

theorem Model.eval_translate (f : S ⟶ T) (M : Model D T) (p : Program S A) :
    M.eval (p.translate f) = (M.reduct f).eval p :=
  Proofs.Logic.BrookesSC.eval_translate f M p

theorem Model.eval_mono {M N : Model D S} (h : M ⟶ N) (p : Program S A) :
    (D.order A).le (M.eval p) (N.eval p) :=
  Proofs.Logic.BrookesSC.eval_mono h p

@[simp] theorem Model.reductFunctor_id (D : Target.{u,v} W) :
    reductFunctor D (𝟙 S) = 𝟭 (Model D S) := rfl

@[simp] theorem Model.reductFunctor_comp (D : Target.{u,v} W) (f : S ⟶ T) (g : T ⟶ U) :
    reductFunctor D (f ≫ g) = reductFunctor D g ⋙ reductFunctor D f := rfl

@[simp] theorem Sentence.translate_id (e : Sentence S) : e.translate (𝟙 S) = e :=
  Proofs.Logic.BrookesSC.sentence_translate_id e

@[simp] theorem Sentence.translate_comp (f : S ⟶ T) (g : T ⟶ U) (e : Sentence S) :
    e.translate (f ≫ g) = (e.translate f).translate g :=
  Proofs.Logic.BrookesSC.sentence_translate_comp f g e

theorem Sentence.satisfaction (f : S ⟶ T) (M : Model D T) (e : Sentence S) :
    (e.translate f).Satisfies M ↔ e.Satisfies (M.reduct f) :=
  Proofs.Logic.BrookesSC.satisfaction f M e

/-- SC program inequations as rooms. The standard covariant sentence and
contravariant model functors are projections of this institution. -/
@[expose] def institution (D : Target.{u,v} W) : Signature W ⥤ Room where
  obj S := ⟨Sentence S, Cat.of (Model D S), Sentence.Satisfies⟩
  map f := ⟨Sentence.translate f, Model.reductFunctor D f, Sentence.satisfaction f⟩
  map_id _ := Room.hom_ext (funext Sentence.translate_id) (Model.reductFunctor_id D)
  map_comp f g := Room.hom_ext (funext (Sentence.translate_comp f g)) (Model.reductFunctor_comp D f g)

end Silmaril.Logic.BrookesSC
