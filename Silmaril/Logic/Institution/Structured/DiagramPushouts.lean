module

public import Silmaril.Logic.Institution.Structured.DiagramKan
public import Mathlib.CategoryTheory.Category.Cat.Colimit
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

set_option backward.isDefEq.respectTransparency false

@[expose] public section
namespace Silmaril.Logic.Institution.CoDiagram
open CategoryTheory CategoryTheory.Limits
universe u w x
noncomputable section
variable {C : Type w} [Category.{x} C]
variable {A B D : CoDiagram.{u,u} C} (f : A ⟶ B) (g : A ⟶ D)

/-- The node category of a diagram pushout is the actual pushout of node categories. -/
def pushoutShape : Cat.{u,u} := pushout f.Φ.toCatHom g.Φ.toCatHom

def leftShape : B.Sign ⥤ pushoutShape f g :=
  (pushout.inl f.Φ.toCatHom g.Φ.toCatHom).toFunctor

def rightShape : D.Sign ⥤ pushoutShape f g :=
  (pushout.inr f.Φ.toCatHom g.Φ.toCatHom).toFunctor

theorem shape_condition : f.Φ ⋙ leftShape f g = g.Φ ⋙ rightShape f g :=
  congrArg Cat.Hom.toFunctor (pushout.condition (f := f.Φ.toCatHom) (g := g.Φ.toCatHom))

def commonShape : A.Sign ⥤ pushoutShape f g := f.Φ ⋙ leftShape f g

variable [HasColimitsOfSize.{u,u} C]

def leftValue : pushoutShape f g ⥤ C := (leftShape f g).leftKanExtension B.I
def rightValue : pushoutShape f g ⥤ C := (rightShape f g).leftKanExtension D.I
def commonValue : pushoutShape f g ⥤ C := (commonShape f g).leftKanExtension A.I

/-- Move the left input transformation onto the glued node category. -/
def leftInput : A.I ⟶ commonShape f g ⋙ leftValue f g :=
  f.ρ ≫ Functor.whiskerLeft f.Φ ((leftShape f g).leftKanExtensionUnit B.I) ≫
    (Functor.associator f.Φ (leftShape f g) (leftValue f g)).inv

/-- Move the right input transformation onto the same glued node category. -/
def rightInput : A.I ⟶ commonShape f g ⋙ rightValue f g :=
  g.ρ ≫ Functor.whiskerLeft g.Φ ((rightShape f g).leftKanExtensionUnit D.I) ≫
    (Functor.associator g.Φ (rightShape f g) (rightValue f g)).inv ≫
    eqToHom (congrArg (fun K => K ⋙ rightValue f g) (shape_condition f g).symm)

def leftLeg : commonValue f g ⟶ leftValue f g :=
  Functor.descOfIsLeftKanExtension _ ((commonShape f g).leftKanExtensionUnit A.I) _ (leftInput f g)

def rightLeg : commonValue f g ⟶ rightValue f g :=
  Functor.descOfIsLeftKanExtension _ ((commonShape f g).leftKanExtensionUnit A.I) _ (rightInput f g)

/-- The proposed value diagram is the pointwise pushout of the Kan-extended inputs. -/
def pushoutDiagram : CoDiagram.{u,u} C :=
  ⟨pushoutShape f g, pushout (leftLeg f g) (rightLeg f g)⟩

def pushoutLeft : B ⟶ pushoutDiagram f g where
  Φ := leftShape f g
  ρ := (leftShape f g).leftKanExtensionUnit B.I ≫
    Functor.whiskerLeft (leftShape f g) (pushout.inl (leftLeg f g) (rightLeg f g))

def pushoutRight : D ⟶ pushoutDiagram f g where
  Φ := rightShape f g
  ρ := (rightShape f g).leftKanExtensionUnit D.I ≫
    Functor.whiskerLeft (rightShape f g) (pushout.inr (leftLeg f g) (rightLeg f g))


theorem pushout_condition : f ≫ pushoutLeft f g = g ≫ pushoutRight f g := by
  apply Diagram.CoHom.ext (f := f ≫ pushoutLeft f g) (g := g ≫ pushoutRight f g)
    (shape_condition f g)
  apply NatTrans.ext
  funext node
  have hL : (commonShape f g).leftKanExtensionUnit A.I ≫
      Functor.whiskerLeft (commonShape f g) (leftLeg f g) = leftInput f g :=
    Functor.descOfIsLeftKanExtension_fac _
    ((commonShape f g).leftKanExtensionUnit A.I) _ (leftInput f g)
  have hR : (commonShape f g).leftKanExtensionUnit A.I ≫
      Functor.whiskerLeft (commonShape f g) (rightLeg f g) = rightInput f g :=
    Functor.descOfIsLeftKanExtension_fac _
    ((commonShape f g).leftKanExtensionUnit A.I) _ (rightInput f g)
  have h : (commonShape f g).leftKanExtensionUnit A.I ≫
      Functor.whiskerLeft (commonShape f g) (leftLeg f g ≫ pushout.inl (leftLeg f g) (rightLeg f g)) =
      (commonShape f g).leftKanExtensionUnit A.I ≫
      Functor.whiskerLeft (commonShape f g) (rightLeg f g ≫ pushout.inr (leftLeg f g) (rightLeg f g)) :=
    congrArg (fun η => ((commonShape f g).leftKanExtensionUnit A.I) ≫
      Functor.whiskerLeft (commonShape f g) η)
    (pushout.condition (f := leftLeg f g) (g := rightLeg f g))
  have h' : leftInput f g ≫ Functor.whiskerLeft (commonShape f g) (pushout.inl (leftLeg f g) (rightLeg f g)) =
      rightInput f g ≫ Functor.whiskerLeft (commonShape f g) (pushout.inr (leftLeg f g) (rightLeg f g)) := by
    simpa only [Functor.whiskerLeft_comp, ← Category.assoc, hL, hR] using h
  have hx : (leftInput f g).app node ≫
      (pushout.inl (leftLeg f g) (rightLeg f g)).app ((commonShape f g).obj node) =
      (rightInput f g).app node ≫
      (pushout.inr (leftLeg f g) (rightLeg f g)).app ((commonShape f g).obj node) :=
    congrArg (fun η => η.app node) h'
  simp only [leftInput, rightInput, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Functor.comp_obj, eqToHom_app,
    Category.assoc] at hx
  have eqnode : (commonShape f g).obj node = (g.Φ ⋙ rightShape f g).obj node :=
    congrArg (fun K => K.obj node) (shape_condition f g)
  have hr := (pushout.inr (leftLeg f g) (rightLeg f g)).naturality (eqToHom eqnode.symm)
  simp only [eqToHom_map] at hr
  rw [hr] at hx
  simp only [commonShape, leftValue, rightValue, Functor.comp_obj, Category.id_comp] at hx
  simp only [CoDiagram.comp_app, pushoutLeft, pushoutRight, NatTrans.comp_app,
    Functor.whiskerLeft_app, eqToHom_app]
  apply (cancel_mono (eqToHom (congrArg (fun n => (pushout (leftLeg f g) (rightLeg f g)).obj n) eqnode.symm))).1
  simpa only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id,
    Category.id_comp] using hx

/-- The genuine commuting cocone; its universal property is proved separately. -/
def pushoutCocone : PushoutCocone f g :=
  PushoutCocone.mk (pushoutLeft f g) (pushoutRight f g) (pushout_condition f g)

/-- The shape map of the mediator into an arbitrary diagram cocone. -/
def descShape (s : PushoutCocone f g) : pushoutShape f g ⥤ s.pt.Sign :=
  (pushout.desc s.inl.Φ.toCatHom s.inr.Φ.toCatHom
    (congrArg (fun h => h.Φ.toCatHom) s.condition)).toFunctor

omit [HasColimitsOfSize.{u,u} C] in
theorem left_descShape (s : PushoutCocone f g) :
    leftShape f g ⋙ descShape f g s = s.inl.Φ :=
  congrArg Cat.Hom.toFunctor (pushout.inl_desc (f := f.Φ.toCatHom) (g := g.Φ.toCatHom)
    s.inl.Φ.toCatHom s.inr.Φ.toCatHom (congrArg (fun h => h.Φ.toCatHom) s.condition))

omit [HasColimitsOfSize.{u,u} C] in
theorem right_descShape (s : PushoutCocone f g) :
    rightShape f g ⋙ descShape f g s = s.inr.Φ :=
  congrArg Cat.Hom.toFunctor (pushout.inr_desc (f := f.Φ.toCatHom) (g := g.Φ.toCatHom)
    s.inl.Φ.toCatHom s.inr.Φ.toCatHom (congrArg (fun h => h.Φ.toCatHom) s.condition))

/-- Transport the left cocone map along the universal shape factorization. -/
def leftTarget (s : PushoutCocone f g) :
    B.I ⟶ leftShape f g ⋙ descShape f g s ⋙ s.pt.I :=
  s.inl.ρ ≫ eqToHom (congrArg (fun K => K ⋙ s.pt.I) (left_descShape f g s).symm) ≫
    (Functor.associator (leftShape f g) (descShape f g s) s.pt.I).hom

/-- Transport the right cocone map along the universal shape factorization. -/
def rightTarget (s : PushoutCocone f g) :
    D.I ⟶ rightShape f g ⋙ descShape f g s ⋙ s.pt.I :=
  s.inr.ρ ≫ eqToHom (congrArg (fun K => K ⋙ s.pt.I) (right_descShape f g s).symm) ≫
    (Functor.associator (rightShape f g) (descShape f g s) s.pt.I).hom

/-- Descend the left transformation through its actual Kan extension. -/
def leftDesc (s : PushoutCocone f g) : leftValue f g ⟶ descShape f g s ⋙ s.pt.I :=
  Functor.descOfIsLeftKanExtension _ ((leftShape f g).leftKanExtensionUnit B.I) _
    (leftTarget f g s)

/-- Descend the right transformation through its actual Kan extension. -/
def rightDesc (s : PushoutCocone f g) : rightValue f g ⟶ descShape f g s ⋙ s.pt.I :=
  Functor.descOfIsLeftKanExtension _ ((rightShape f g).leftKanExtensionUnit D.I) _
    (rightTarget f g s)

theorem leftDesc_fac (s : PushoutCocone f g) :
    (leftShape f g).leftKanExtensionUnit B.I ≫
      Functor.whiskerLeft (leftShape f g) (leftDesc f g s) = leftTarget f g s :=
  Functor.descOfIsLeftKanExtension_fac _ _ _ _

theorem rightDesc_fac (s : PushoutCocone f g) :
    (rightShape f g).leftKanExtensionUnit D.I ≫
      Functor.whiskerLeft (rightShape f g) (rightDesc f g s) = rightTarget f g s :=
  Functor.descOfIsLeftKanExtension_fac _ _ _ _

omit [HasColimitsOfSize.{u,u} C] in
private theorem cohom_transport {E F : CoDiagram.{u,u} C} {a b : E ⟶ F}
    (h : a = b) (hp : a.Φ = b.Φ) :
    a.ρ ≫ eqToHom (congrArg (fun K => K ⋙ F.I) hp) = b.ρ := by
  cases h
  simp only [eqToHom_refl, Category.comp_id]

theorem legs_desc (s : PushoutCocone f g) :
    leftLeg f g ≫ leftDesc f g s = rightLeg f g ≫ rightDesc f g s := by
  apply Functor.hom_ext_of_isLeftKanExtension _ ((commonShape f g).leftKanExtensionUnit A.I)
  simp only [Functor.whiskerLeft_comp, ← Category.assoc]
  simp only [leftLeg, rightLeg, Functor.descOfIsLeftKanExtension_fac]
  apply NatTrans.ext
  funext node
  simp only [leftInput, rightInput, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, eqToHom_app]
  have eqnode : (commonShape f g).obj node = (g.Φ ⋙ rightShape f g).obj node :=
    congrArg (fun K => K.obj node) (shape_condition f g)
  have hr := (rightDesc f g s).naturality (eqToHom eqnode.symm)
  simp only [eqToHom_map, commonShape, Functor.comp_obj] at hr
  simp only [commonShape, leftValue, rightValue, Functor.comp_obj,
    Category.comp_id, Category.id_comp, Category.assoc]
  rw [hr]
  have hlf : ((leftShape f g).leftKanExtensionUnit B.I).app (f.Φ.obj node) ≫
      (leftDesc f g s).app ((leftShape f g).obj (f.Φ.obj node)) =
      (leftTarget f g s).app (f.Φ.obj node) :=
    congrArg (fun η => η.app (f.Φ.obj node)) (leftDesc_fac f g s)
  have hrf : ((rightShape f g).leftKanExtensionUnit D.I).app (g.Φ.obj node) ≫
      (rightDesc f g s).app ((rightShape f g).obj (g.Φ.obj node)) =
      (rightTarget f g s).app (g.Φ.obj node) :=
    congrArg (fun η => η.app (g.Φ.obj node)) (rightDesc_fac f g s)
  rw [hlf]
  rw [← Category.assoc _ ((rightDesc f g s).app ((rightShape f g).obj (g.Φ.obj node))) _, hrf]
  simp only [leftTarget, rightTarget, NatTrans.comp_app, eqToHom_app,
    Functor.associator_hom_app, Category.assoc, Category.comp_id]
  have hs : (f ≫ s.inl).ρ ≫ eqToHom
      (congrArg (fun K => K ⋙ s.pt.I) (congrArg (fun h => h.Φ) s.condition)) =
      (g ≫ s.inr).ρ := cohom_transport s.condition
    (congrArg (fun h => h.Φ) s.condition)
  have hsn : ((f ≫ s.inl).ρ ≫ eqToHom
      (congrArg (fun K => K ⋙ s.pt.I) (congrArg (fun h => h.Φ) s.condition))).app node =
      (g ≫ s.inr).ρ.app node := congrArg (fun η => η.app node) hs
  simp only [CoDiagram.comp_app, NatTrans.comp_app, eqToHom_app] at hsn
  simp only [← Category.assoc]
  rw [← hsn]
  simp only [Category.assoc, eqToHom_trans]



/-- The actual diagram mediator, combining Kan descent with the pointwise pushout. -/
def pushoutDesc (s : PushoutCocone f g) : pushoutDiagram f g ⟶ s.pt where
  Φ := descShape f g s
  ρ := pushout.desc (leftDesc f g s) (rightDesc f g s) (legs_desc f g s)

theorem pushoutLeft_desc (s : PushoutCocone f g) :
    pushoutLeft f g ≫ pushoutDesc f g s = s.inl := by
  apply Diagram.CoHom.ext (f := pushoutLeft f g ≫ pushoutDesc f g s) (g := s.inl)
    (left_descShape f g s)
  apply NatTrans.ext
  funext node
  have h := congrArg (fun η => η.app node) (leftDesc_fac f g s)
  have hp := congrArg (fun η => η.app ((leftShape f g).obj node))
    (pushout.inl_desc (leftDesc f g s) (rightDesc f g s) (legs_desc f g s))
  simp only [CoDiagram.comp_app, pushoutLeft, pushoutDesc, NatTrans.comp_app,
    Functor.whiskerLeft_app, eqToHom_app]
  simp only [NatTrans.comp_app] at hp
  simp only [Category.assoc]
  rw [← Category.assoc ((pushout.inl (leftLeg f g) (rightLeg f g)).app _) _ _, hp]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
  rw [← Category.assoc, h]
  simp only [leftTarget, NatTrans.comp_app, eqToHom_app, Functor.associator_hom_app,
    Category.assoc, Category.comp_id, eqToHom_trans, eqToHom_refl]

theorem pushoutRight_desc (s : PushoutCocone f g) :
    pushoutRight f g ≫ pushoutDesc f g s = s.inr := by
  apply Diagram.CoHom.ext (f := pushoutRight f g ≫ pushoutDesc f g s) (g := s.inr)
    (right_descShape f g s)
  apply NatTrans.ext
  funext node
  have h := congrArg (fun η => η.app node) (rightDesc_fac f g s)
  have hp := congrArg (fun η => η.app ((rightShape f g).obj node))
    (pushout.inr_desc (leftDesc f g s) (rightDesc f g s) (legs_desc f g s))
  simp only [CoDiagram.comp_app, pushoutRight, pushoutDesc, NatTrans.comp_app,
    Functor.whiskerLeft_app, eqToHom_app]
  simp only [NatTrans.comp_app] at hp
  simp only [Category.assoc]
  rw [← Category.assoc ((pushout.inr (leftLeg f g) (rightLeg f g)).app _) _ _, hp]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
  rw [← Category.assoc, h]
  simp only [rightTarget, NatTrans.comp_app, eqToHom_app, Functor.associator_hom_app,
    Category.assoc, Category.comp_id, eqToHom_trans, eqToHom_refl]

theorem pushoutDesc_unique (s : PushoutCocone f g) (m : pushoutDiagram f g ⟶ s.pt)
    (hl : pushoutLeft f g ≫ m = s.inl) (hr : pushoutRight f g ≫ m = s.inr) :
    m = pushoutDesc f g s := by
  rcases m with ⟨M, μ⟩
  have hM : M = descShape f g s := by
    have he : M.toCatHom = (descShape f g s).toCatHom := by
      apply pushout.hom_ext (f := f.Φ.toCatHom) (g := g.Φ.toCatHom)
      · exact (congrArg (fun k => k.Φ.toCatHom) hl).trans
          (congrArg Functor.toCatHom (left_descShape f g s)).symm
      · exact (congrArg (fun k => k.Φ.toCatHom) hr).trans
          (congrArg Functor.toCatHom (right_descShape f g s)).symm
    exact congrArg Cat.Hom.toFunctor he
  subst M
  apply Diagram.CoHom.ext (f := ⟨descShape f g s, μ⟩) (g := pushoutDesc f g s) rfl
  simp only [eqToHom_refl, Category.comp_id]
  change μ = pushout.desc (leftDesc f g s) (rightDesc f g s) (legs_desc f g s)
  apply pushout.hom_ext
  · show pushout.inl (leftLeg f g) (rightLeg f g) ≫ μ =
        pushout.inl (leftLeg f g) (rightLeg f g) ≫
        pushout.desc (leftDesc f g s) (rightDesc f g s) (legs_desc f g s)
    rw [pushout.inl_desc]
    apply Functor.hom_ext_of_isLeftKanExtension _ ((leftShape f g).leftKanExtensionUnit B.I)
    rw [leftDesc_fac]
    apply NatTrans.ext
    funext node
    have ht : (pushoutLeft f g ≫ ⟨descShape f g s, μ⟩).ρ ≫
        eqToHom (congrArg (fun K => K ⋙ s.pt.I) (left_descShape f g s)) = s.inl.ρ :=
      cohom_transport hl (left_descShape f g s)
    have htn : ((pushoutLeft f g ≫ ⟨descShape f g s, μ⟩).ρ ≫
        eqToHom (congrArg (fun K => K ⋙ s.pt.I) (left_descShape f g s))).app node =
        s.inl.ρ.app node := congrArg (fun η => η.app node) ht
    apply (cancel_mono (eqToHom
      (congrArg (fun K => (K ⋙ s.pt.I).obj node) (left_descShape f g s)))).1
    simpa only [CoDiagram.comp_app, pushoutLeft, NatTrans.comp_app,
      Functor.whiskerLeft_app, leftTarget, Functor.associator_hom_app,
      eqToHom_app, Category.assoc, eqToHom_trans, eqToHom_refl,
      Category.comp_id] using htn
  · show pushout.inr (leftLeg f g) (rightLeg f g) ≫ μ =
        pushout.inr (leftLeg f g) (rightLeg f g) ≫
        pushout.desc (leftDesc f g s) (rightDesc f g s) (legs_desc f g s)
    rw [pushout.inr_desc]
    apply Functor.hom_ext_of_isLeftKanExtension _ ((rightShape f g).leftKanExtensionUnit D.I)
    rw [rightDesc_fac]
    apply NatTrans.ext
    funext node
    have ht : (pushoutRight f g ≫ ⟨descShape f g s, μ⟩).ρ ≫
        eqToHom (congrArg (fun K => K ⋙ s.pt.I) (right_descShape f g s)) = s.inr.ρ :=
      cohom_transport hr (right_descShape f g s)
    have htn : ((pushoutRight f g ≫ ⟨descShape f g s, μ⟩).ρ ≫
        eqToHom (congrArg (fun K => K ⋙ s.pt.I) (right_descShape f g s))).app node =
        s.inr.ρ.app node := congrArg (fun η => η.app node) ht
    apply (cancel_mono (eqToHom
      (congrArg (fun K => (K ⋙ s.pt.I).obj node) (right_descShape f g s)))).1
    simpa only [CoDiagram.comp_app, pushoutRight, NatTrans.comp_app,
      Functor.whiskerLeft_app, rightTarget, Functor.associator_hom_app,
      eqToHom_app, Category.assoc, eqToHom_trans, eqToHom_refl,
      Category.comp_id] using htn

/-- The glued cocone is an actual pushout of varying-shape diagrams
(Durán–Meseguer 1999, Lemma 3.4). -/
def pushoutIsColimit : IsColimit (pushoutCocone f g) :=
  PushoutCocone.IsColimit.mk (pushout_condition f g) (pushoutDesc f g)
    (pushoutLeft_desc f g) (pushoutRight_desc f g) (pushoutDesc_unique f g)

instance hasPushout : HasPushout f g :=
  HasColimit.mk ⟨pushoutCocone f g, pushoutIsColimit f g⟩

instance hasPushouts : HasPushouts (CoDiagram.{u,u} C) :=
  hasPushouts_of_hasColimit_span (CoDiagram.{u,u} C)

end
end Silmaril.Logic.Institution.CoDiagram
