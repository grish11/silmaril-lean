module

public import Silmaril.Logic.CommonLogic.FiniteListFOL.Defs

@[expose] public section
namespace Silmaril.Proofs.Logic.CommonLogic.FiniteListFOL
universe u u' v v'
open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Examples
open Silmaril.Logic.CommonLogic
open Silmaril.Logic.CommonLogic.FiniteListFOL
open Silmaril.Logic.FirstOrder

/-- Constructor equations determine append on every actual finite list. -/
theorem append_evaluation {S : Core.Signature} (M : Model S)
    (xs ys : List (D M.obj)) :
    append M.obj (FiniteLists.evaluationEquiv M.obj xs)
      (FiniteLists.evaluationEquiv M.obj ys) =
        FiniteLists.evaluationEquiv M.obj (xs ++ ys) := by
  simp only [FiniteLists.evaluationEquiv_apply]
  induction xs with
  | nil => exact M.property.append_nil _
  | cons x xs ih =>
    change append M.obj ((FiniteLists.listReduct M.obj.obj).cons x _) _ =
      (FiniteLists.listReduct M.obj.obj).cons x _
    erw [M.property.append_cons, ih]
    rfl

/-- Exact object expansion, not merely an isomorphism of decoded carriers. -/
theorem decode_expand {S : Core.Signature} (M : Core.Model S) : decode (expand M) = M := by
  change ({ M with
    sequence := fun n => (FiniteLists.evaluationEquiv (native M).toModel).symm (M.sequence n)
    function := fun r xs => M.function r (FiniteLists.evaluationEquiv (native M).toModel xs)
    relation := fun r xs => M.relation r (FiniteLists.evaluationEquiv (native M).toModel xs)
  } : Core.Model S) = M
  have hs : (fun n => (FiniteLists.evaluationEquiv (native M).toModel).symm (M.sequence n)) =
      M.sequence := funext fun n => (native M).evaluation_symm (M.sequence n)
  have hf : (fun r xs => M.function r (FiniteLists.evaluationEquiv (native M).toModel xs)) =
      M.function := funext fun r => funext fun xs => congrArg (M.function r) ((native M).evaluation xs)
  have hr : (fun r xs => M.relation r (FiniteLists.evaluationEquiv (native M).toModel xs)) =
      M.relation := funext fun r => funext fun xs => congrArg (M.relation r) ((native M).evaluation xs)
  erw [hs, hf, hr]

private theorem tuple_map {S : Core.Signature} {M N : Target S}
    (h : M.obj ⟶ N.obj) (a b : FiniteLists.ListSort)
    (x : M.obj.carrier a) (y : M.obj.carrier b) :
    (fun i => h.map (FiniteLists.pair a b i) (Fin.cases x (fun _ => y) i)) =
      Fin.cases (h.map a x) (fun _ => h.map b y) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem map_constant {S : Core.Signature} {M N : Target S}
    (h : M.obj ⟶ N.obj) {s : FiniteLists.ListSort} (o : Op S 0 Fin.elim0 s) :
    h.map s (M.obj.op (.extra o) (fun i => Fin.elim0 i)) = N.obj.op (.extra o) (fun i => Fin.elim0 i) := by
  rw [h.map_op]
  congr 1
  funext i
  exact Fin.elim0 i

theorem map_embed {S : Core.Signature} {M N : Target S}
    (h : M.obj ⟶ N.obj) (x : D M) :
    h.map .reference (embed M x) = embed N (h.map .discourse x) :=
  h.map_op (.extra .embed) (fun _ => x)

theorem map_apply {S : Core.Signature} {M N : Target S}
    (h : M.obj ⟶ N.obj) (r : R M) (xs : L M) :
    h.map .discourse (apply M r xs) = apply N (h.map .reference r) (h.map .sequence xs) := by
  unfold apply
  rw [h.map_op, tuple_map]

theorem map_holds {S : Core.Signature} {M N : Target S}
    (h : M.obj ⟶ N.obj) (r : R M) (xs : L M) (hr : holds M r xs) :
    holds N (h.map .reference r) (h.map .sequence xs) := by
  unfold holds at hr ⊢
  have hr' := h.map_rel (n := 2) (w := FiniteLists.pair .reference .sequence)
    Rel.holds _ hr
  rw [tuple_map] at hr'
  exact hr'

theorem inverse_evaluation_natural {S : Core.Signature} (M N : Target S)
    (h : M.obj ⟶ N.obj) (xs : L M) :
    ((FiniteLists.evaluationEquiv M).symm xs).map (h.map .discourse) =
      (FiniteLists.evaluationEquiv N).symm (h.map .sequence xs) := by
  apply (FiniteLists.evaluationEquiv N).injective
  rw [(FiniteLists.evaluationEquiv N).apply_symm_apply]
  rw [← FiniteLists.evaluation_natural M N h]
  rw [(FiniteLists.evaluationEquiv M).apply_symm_apply]

/-- Relation preservation remains one-way, exactly as in public FOL and Core. -/
def decodeHom {S : Core.Signature} {M N : Model S} (h : M ⟶ N) :
    decode M ⟶ decode N where
  reference := h.hom.hom.map .reference
  discourse := h.hom.hom.map .discourse
  embed := map_embed h.hom.hom
  name n := map_constant h.hom.hom (.discourse n)
  nonname n := map_constant h.hom.hom (.nondiscourse n)
  sequence m := by
    change ((FiniteLists.evaluationEquiv M.obj).symm (marker M.obj m)).map
      (h.hom.hom.map .discourse) = (FiniteLists.evaluationEquiv N.obj).symm (marker N.obj m)
    rw [inverse_evaluation_natural M.obj N.obj h.hom.hom]
    exact congrArg (FiniteLists.evaluationEquiv N.obj).symm
      (map_constant h.hom.hom (.marker m))
  function r xs := by
    change h.hom.hom.map .discourse
      (apply M.obj r (FiniteLists.evaluationEquiv M.obj xs)) =
        apply N.obj (h.hom.hom.map .reference r)
          (FiniteLists.evaluationEquiv N.obj (xs.map (h.hom.hom.map .discourse)))
    exact (map_apply h.hom.hom r (FiniteLists.evaluationEquiv M.obj xs)).trans
      (congrArg (apply N.obj (h.hom.hom.map .reference r))
        (FiniteLists.evaluation_natural M.obj N.obj h.hom.hom xs))
  relation r xs hr := by
    have hn := map_holds h.hom.hom r (FiniteLists.evaluationEquiv M.obj xs) hr
    exact (congrArg (holds N.obj (h.hom.hom.map .reference r))
      (FiniteLists.evaluation_natural M.obj N.obj h.hom.hom xs)).mp hn

noncomputable def models (S : Core.Signature) : Model S ⥤ Core.Model S where
  obj := decode
  map := decodeHom
  map_id _ := Core.Model.Hom.ext _ _ rfl rfl
  map_comp _ _ := Core.Model.Hom.ext _ _ rfl rfl

/-- Constant-symbol reducts leave the full underlying list algebra unchanged. -/
theorem decode_reduct {S T : Core.Signature} (f : S ⟶ T) (M : Model T) :
    decode ((reduct f).obj M) = (Core.Model.reduct f).obj (decode M) := rfl

theorem signatureMap_id (S : Core.Signature) : signatureMap (𝟙 S) = 𝟙 (signature S) := by
  apply FiniteLists.Signature.Hom.ext
  · funext n w s o
    cases o <;> rfl
  · funext n w r
    cases r; rfl

theorem signatureMap_comp {S T U : Core.Signature} (f : S ⟶ T) (g : T ⟶ U) :
    signatureMap (f ≫ g) = signatureMap f ≫ signatureMap g := by
  apply FiniteLists.Signature.Hom.ext
  · funext n w s o
    cases o <;> rfl
  · funext n w r
    cases r; rfl

/-- Equality of full-subcategory functors can be checked after forgetting the
property proof. This avoids rewriting through a dependent lift proof field. -/
private theorem fullSubcategory_functor_ext {C : Type u} {D : Type u'}
    [Category.{v} C] [Category.{v'} D]
    (Q : ObjectProperty D) {F G : C ⥤ Q.FullSubcategory}
    (h : F ⋙ Q.ι = G ⋙ Q.ι) : F = G := by
  have hobj : ∀ X, F.obj X = G.obj X := fun X =>
    ObjectProperty.FullSubcategory.ext (congrArg (fun K => K.obj X) h)
  refine CategoryTheory.Functor.ext hobj ?_
  intro X Y f
  apply Q.ι.map_injective
  simpa only [Functor.comp_map, Functor.map_comp, eqToHom_map] using
    Functor.congr_hom h f


theorem reduct_id (S : Core.Signature) : reduct (𝟙 S) = 𝟭 (Model S) := by
  apply fullSubcategory_functor_ext (Constraints (S := S))
  change (Constraints (S := S)).ι ⋙ FiniteLists.reduct (signatureMap (𝟙 S)) =
    (Constraints (S := S)).ι
  rw [signatureMap_id, FiniteLists.reduct_id]
  rfl

theorem reduct_comp {S T U : Core.Signature} (f : S ⟶ T) (g : T ⟶ U) :
    reduct (f ≫ g) = reduct g ⋙ reduct f := by
  apply fullSubcategory_functor_ext (Constraints (S := S))
  change (Constraints (S := U)).ι ⋙ FiniteLists.reduct (signatureMap (f ≫ g)) =
    ((Constraints (S := U)).ι ⋙ FiniteLists.reduct (signatureMap g)) ⋙
      FiniteLists.reduct (signatureMap f)
  rw [signatureMap_comp, FiniteLists.reduct_comp]
  rfl

theorem corridor_id (S : Core.Signature) : corridor (𝟙 S) = 𝟙 (room S) := by
  apply Silmaril.Logic.Institution.Room.hom_ext
  · funext p
    change FOL.Sentence.map (FiniteLists.publicMap (signatureMap (𝟙 S))) p = p
    rw [signatureMap_id, FiniteLists.publicMap_id]
    exact FOL.Sentence.map_id p
  · exact reduct_id S

theorem corridor_comp {S T U : Core.Signature} (f : S ⟶ T) (g : T ⟶ U) :
    corridor (f ≫ g) = corridor f ≫ corridor g := by
  apply Silmaril.Logic.Institution.Room.hom_ext
  · funext p
    change FOL.Sentence.map (FiniteLists.publicMap (signatureMap (f ≫ g))) p =
      FOL.Sentence.map (FiniteLists.publicMap (signatureMap g))
        (FOL.Sentence.map (FiniteLists.publicMap (signatureMap f)) p)
    rw [signatureMap_comp, FiniteLists.publicMap_comp]
    exact FOL.Sentence.map_comp _ _ p
  · exact reduct_comp f g

/-- Equality includes the underlying maps of every original FOL arrow. -/
theorem models_natural {S T : Core.Signature} (f : S ⟶ T) :
    reduct f ⋙ models S = models T ⋙ Core.Model.reduct f := rfl

end Silmaril.Proofs.Logic.CommonLogic.FiniteListFOL
