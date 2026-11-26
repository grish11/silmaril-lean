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

theorem Sentence.translateLift_eq (f : S ⟶ T) (φ : Sentence.{u,v} S) : φ.translateLift f.hom = φ.translate f :=
  Proofs.translateLift_eq f φ

@[simp] theorem Sentence.translateLift_id (φ : Sentence.{u,v} S) :
    φ.translateLift (𝟙 S.toSignature) = φ :=
  Proofs.translateLift_id φ

/-- The whole predicate and the translated tree agree under composition. -/
theorem Sentence.translateLift_comp (f : S.toSignature ⟶ T.toSignature) (g : T.toSignature ⟶ U.toSignature)
    (φ : Sentence.{u,v} S) : φ.translateLift (f ≫ g) = (φ.translateLift f).translateLift g :=
  Proofs.translateLift_comp f g φ

/-- Lifted translation uses the same initial state and admits each alias
along its own handler transitions. Injective complete keys suffice. -/
theorem satisfaction_lift_at (f : S.toSignature ⟶ T.toSignature) (keys : Function.Injective f.request)
    (M : Model.{u,w} T.toSignature) (φ : Sentence.{u,v} S) (x : M.State) :
    SatAt M (φ.translateLift f) x ↔ SatAt (M.reduct f) φ x :=
  Proofs.satisfaction_lift_at f keys M φ x

/-- The existing reduct satisfies the per-model condition with the
all-lifts predicate translation, even for non-injective reply maps. -/
theorem satisfaction_lift (f : S.toSignature ⟶ T.toSignature) (keys : Function.Injective f.request)
    (M : Model.{u,w} T.toSignature) (φ : Sentence.{u,v} S) :
    Sat M (φ.translateLift f) ↔ Sat (M.reduct f) φ :=
  forall_congr' fun x => imp_congr_right fun _ => satisfaction_lift_at f keys M φ x

theorem sat_renameState (M : Model.{u,w} S.toSignature) {Y : Type w} (e : M.State ≃ Y)
    (φ : Sentence.{u,v} S) : Sat (M.renameState e) φ ↔ Sat M φ :=
  Proofs.sat_renameState M e φ

/-- A trace sentence is valid in every shared handler exactly when the
unrestricted handler satisfies it. -/
theorem valid_iff_sat_allReplies (φ : Sentence.{u,v} S) :
    (∀ M : Model.{u,0} S.toSignature, Sat M φ) ↔ Sat (allRepliesModel S) φ :=
  Proofs.valid_iff_sat_allReplies φ

theorem sat_allReplies_hasTrace_iff {A : Type v} (source target : Tree S.toSignature.Event A) :
    Sat (allRepliesModel S) ⟨A, source, HasTrace target⟩ ↔ TraceLE source target :=
  Proofs.sat_allReplies_hasTrace_iff source target

/-- A refinement sentence is valid under every shared handler precisely
when the unrestricted trace inclusion holds. -/
theorem valid_hasTrace_iff {A : Type v} (source target : Tree S.toSignature.Event A) :
    (∀ M : Model.{u, 0} S.toSignature, Sat M ⟨A, source, HasTrace target⟩) ↔ TraceLE source target :=
  (valid_iff_sat_allReplies _).trans (sat_allReplies_hasTrace_iff source target)

/-- The lifted acceptance predicate is observation of the actual mapped
target tree, even with reply aliases or omissions. -/
theorem translateLift_hasTrace (f : S.toSignature ⟶ T.toSignature) {A : Type v}
    (l r : Tree S.toSignature.Event A) :
    (⟨A, l, HasTrace r⟩ : Sentence S).translateLift (T := T) f =
      ⟨A, f.tree id l, HasTrace (f.tree id r)⟩ :=
  congrArg (Sentence.mk A (f.tree id l)) (funext fun p => propext (f.hasTrace_lift_iff r p).symm)

/-- Translating a trace-refinement sentence is the sentence comparing the
two translated trees, with their original ordered results. -/
theorem translate_hasTrace (f : S ⟶ T) {A : Type v} (l r : Tree S.toSignature.Event A) :
    (⟨A, l, HasTrace r⟩ : Sentence S).translate f =
      ⟨A, f.hom.tree id l, HasTrace (f.hom.tree id r)⟩ :=
  ((⟨A, l, HasTrace r⟩ : Sentence S).translateLift_eq f).symm.trans (translateLift_hasTrace f.hom l r)

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
