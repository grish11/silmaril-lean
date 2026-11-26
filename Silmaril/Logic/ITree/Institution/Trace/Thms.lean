module

public import Silmaril.Logic.ITree.Institution.Trace.Defs
import Silmaril.Proofs.Logic.ITree.Institution.Trace.Laws

@[expose] public section

namespace Silmaril.Logic.ITree.TraceInstitution

open CategoryTheory Silmaril.Elgot.ITree Opposite

universe u v w

variable {S T U : TraceSignature.{u}}

@[simp] theorem Sentence.translate_id (φ : Sentence.{u,v} S) : φ.translate (𝟙 S) = φ :=
  Proofs.translate_id φ

/-- Predicate composition holds on the entire target observation type. -/
theorem Sentence.accepts_translate_comp (f : S ⟶ T) (g : T ⟶ U) (φ : Sentence.{u,v} S)
    (p : Trace U.toSignature.Event φ.Result) :
    (φ.translate (f ≫ g)).accepts p ↔ ((φ.translate f).translate g).accepts p :=
  Proofs.accepts_translate_comp f g φ p

theorem Sentence.translate_comp (f : S ⟶ T) (g : T ⟶ U) (φ : Sentence.{u,v} S) :
    φ.translate (f ≫ g) = (φ.translate f).translate g :=
  Proofs.translate_comp f g φ

theorem satisfaction_at (f : S ⟶ T) (M : Model.{u,w} T.toSignature) (φ : Sentence.{u,v} S)
    (x : M.State) : SatAt M (φ.translate f) x ↔ SatAt (M.reduct f.hom) φ x :=
  Proofs.satisfaction_at f M φ x

theorem satisfaction (f : S ⟶ T) (M : Model.{u,w} T.toSignature) (φ : Sentence.{u,v} S) :
    Sat M (φ.translate f) ↔ Sat (M.reduct f.hom) φ :=
  forall_congr' fun x => imp_congr_right fun _ => satisfaction_at f M φ x

theorem sat_renameState (M : Model.{u,w} S.toSignature) {Y : Type w} (e : M.State ≃ Y)
    (φ : Sentence.{u,v} S) : Sat (M.renameState e) φ ↔ Sat M φ :=
  Proofs.sat_renameState M e φ

/-- Trace sentences translate covariantly. -/
noncomputable def sentences : TraceSignature.{u} ⥤ Type (max (u + 1) (v + 1)) where
  obj := Sentence.{u,v}
  map f := TypeCat.ofHom (Sentence.translate f)
  map_id _ := congrArg TypeCat.ofHom (funext Sentence.translate_id)
  map_comp f g := congrArg TypeCat.ofHom (funext (Sentence.translate_comp f g))

/-- The model functor is the return institution's model functor restricted to
trace signature arrows. Its fibers are still discrete categories. -/
def models : TraceSignature.{u}ᵒᵖ ⥤ Cat.{max (u + 1) (w + 1), max (u + 1) (w + 1)} :=
  TraceSignature.forget.op ⋙ Silmaril.Logic.ITree.models.{u,w}

/-- The classic institution of finite handled-trace predicates. -/
noncomputable def institution : Silmaril.Logic.Institution.ClassicInstitution.{u + 1, u + 1,
    max (u + 1) (v + 1), max (u + 1) (w + 1), max (u + 1) (w + 1)} TraceSignature.{u} where
  Sen := sentences.{u,v}
  Mod := models.{u,w}
  Sat _ M := Sat M.as
  satisfaction f M := satisfaction f M.as

end Silmaril.Logic.ITree.TraceInstitution
