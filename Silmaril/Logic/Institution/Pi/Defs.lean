module

public import Silmaril.Logic.Institution.Metatheory.Entailment

set_option backward.isDefEq.respectTransparency false

@[expose] public section

namespace Silmaril.Logic.Institution

open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Metatheory

universe u v w x y z

/-- A diagram with a variable category of indices. This is the object data of
both diagram categories in Rios et al., arXiv:2002.00298v2, §2.3. -/
structure Diagram (C : Type w) [Category.{x} C] where
  Sign : Type u
  [cat : Category.{v} Sign]
  I : Sign ⥤ C

attribute [instance] Diagram.cat

namespace Diagram

variable {C : Type w} [Category.{x} C]

/-- Forward translation of diagrams, including a change of index category. -/
structure CoHom (A : Diagram.{u,v} C) (B : Diagram.{y,z} C) where
  Φ : A.Sign ⥤ B.Sign
  ρ : A.I ⟶ Φ ⋙ B.I

/-- Backward translation of diagram values, with a forward index functor. -/
structure Hom (A : Diagram.{u,v} C) (B : Diagram.{y,z} C) where
  Φ : A.Sign ⥤ B.Sign
  η : Φ ⋙ B.I ⟶ A.I

variable {A B D : Diagram.{u,v} C}

def CoHom.id (A : Diagram.{u,v} C) : CoHom A A :=
  ⟨𝟭 _, (Functor.leftUnitor A.I).inv⟩

def CoHom.comp (f : CoHom A B) (g : CoHom B D) : CoHom A D :=
  ⟨f.Φ ⋙ g.Φ, f.ρ ≫ Functor.whiskerLeft f.Φ g.ρ ≫ (Functor.associator f.Φ g.Φ D.I).inv⟩

def Hom.id (A : Diagram.{u,v} C) : Hom A A :=
  ⟨𝟭 _, (Functor.leftUnitor A.I).hom⟩

def Hom.comp (f : Hom A B) (g : Hom B D) : Hom A D :=
  ⟨f.Φ ⋙ g.Φ, (Functor.associator f.Φ g.Φ D.I).hom ≫ Functor.whiskerLeft f.Φ g.η ≫ f.η⟩

theorem CoHom.ext {f g : CoHom A B} (hΦ : f.Φ = g.Φ)
    (hρ : f.ρ ≫ eqToHom (by rw [hΦ]) = g.ρ) : f = g := by
  cases f
  cases g
  cases hΦ
  simp only [eqToHom_refl, Category.comp_id] at hρ
  cases hρ
  rfl

theorem Hom.ext {f g : Hom A B} (hΦ : f.Φ = g.Φ)
    (hη : f.η = eqToHom (by rw [hΦ]) ≫ g.η) : f = g := by
  cases f
  cases g
  cases hΦ
  simp only [eqToHom_refl, Category.id_comp] at hη
  cases hη
  rfl

end Diagram

set_option linter.checkUnivs false in
/-- The category of diagrams with forward transformations (`Diag_co`). -/
def CoDiagram (C : Type w) [Category.{x} C] := Diagram.{u,v} C

set_option linter.checkUnivs false in
/-- The category of diagrams with backward transformations (`Diag_mor`). -/
def MorDiagram (C : Type w) [Category.{x} C] := Diagram.{u,v} C

/-- Signature-category instances remain available through the diagram synonyms. -/
instance CoDiagram.signCategory {C : Type w} [Category.{x} C]
    (A : CoDiagram.{u,v} C) : Category.{v} A.Sign := A.cat

instance MorDiagram.signCategory {C : Type w} [Category.{x} C]
    (A : MorDiagram.{u,v} C) : Category.{v} A.Sign := A.cat

instance CoDiagram.category (C : Type w) [Category.{x} C] :
    Category (CoDiagram.{u,v} C) where
  Hom A B := Diagram.CoHom A B
  id := Diagram.CoHom.id
  comp := Diagram.CoHom.comp
  id_comp f := by
    apply Diagram.CoHom.ext (f := (Diagram.CoHom.id _).comp f) (g := f) rfl
    simp only [eqToHom_refl, Category.comp_id]
    apply NatTrans.ext
    funext S
    simp [Diagram.CoHom.comp, Diagram.CoHom.id]
  comp_id f := by
    apply Diagram.CoHom.ext (f := f.comp (.id _)) (g := f) rfl
    simp only [eqToHom_refl, Category.comp_id]
    apply NatTrans.ext
    funext S
    simp [Diagram.CoHom.comp, Diagram.CoHom.id]
  assoc f g h := by
    apply Diagram.CoHom.ext (f := (f.comp g).comp h) (g := f.comp (g.comp h)) rfl
    simp only [eqToHom_refl, Category.comp_id]
    apply NatTrans.ext
    funext S
    simp [Diagram.CoHom.comp, Category.assoc]

instance MorDiagram.category (C : Type w) [Category.{x} C] :
    Category (MorDiagram.{u,v} C) where
  Hom A B := Diagram.Hom A B
  id := Diagram.Hom.id
  comp := Diagram.Hom.comp
  id_comp f := by
    apply Diagram.Hom.ext (f := (Diagram.Hom.id _).comp f) (g := f) rfl
    simp only [eqToHom_refl, Category.id_comp]
    apply NatTrans.ext
    funext S
    simp [Diagram.Hom.comp, Diagram.Hom.id]
  comp_id f := by
    apply Diagram.Hom.ext (f := f.comp (.id _)) (g := f) rfl
    simp only [eqToHom_refl, Category.id_comp]
    apply NatTrans.ext
    funext S
    simp [Diagram.Hom.comp, Diagram.Hom.id]
  assoc f g h := by
    apply Diagram.Hom.ext (f := (f.comp g).comp h) (g := f.comp (g.comp h)) rfl
    simp only [eqToHom_refl, Category.id_comp]
    apply NatTrans.ext
    funext S
    simp [Diagram.Hom.comp, Category.assoc]

@[simp] theorem CoDiagram.id_phi {C : Type w} [Category.{x} C]
    (A : CoDiagram.{u,v} C) : (𝟙 A : A ⟶ A).Φ = 𝟭 A.Sign := rfl

@[simp] theorem CoDiagram.comp_phi {C : Type w} [Category.{x} C]
    {A B D : CoDiagram.{u,v} C} (f : A ⟶ B) (g : B ⟶ D) :
    (f ≫ g).Φ = f.Φ ⋙ g.Φ := rfl

@[simp] theorem CoDiagram.id_app {C : Type w} [Category.{x} C]
    (A : CoDiagram.{u,v} C) (S : A.Sign) : (𝟙 A : A ⟶ A).ρ.app S = 𝟙 (A.I.obj S) := rfl

@[simp] theorem CoDiagram.comp_app {C : Type w} [Category.{x} C]
    {A B D : CoDiagram.{u,v} C} (f : A ⟶ B) (g : B ⟶ D) (S : A.Sign) :
    (f ≫ g).ρ.app S = f.ρ.app S ≫ g.ρ.app (f.Φ.obj S) := by
  change f.ρ.app S ≫ (g.ρ.app (f.Φ.obj S) ≫ 𝟙 _) = _
  rw [Category.comp_id]

@[simp] theorem MorDiagram.id_app {C : Type w} [Category.{x} C]
    (A : MorDiagram.{u,v} C) (S : A.Sign) : (𝟙 A : A ⟶ A).η.app S = 𝟙 (A.I.obj S) := rfl

@[simp] theorem MorDiagram.comp_app {C : Type w} [Category.{x} C]
    {A B D : MorDiagram.{u,v} C} (f : A ⟶ B) (g : B ⟶ D) (S : A.Sign) :
    (f ≫ g).η.app S = g.η.app (f.Φ.obj S) ≫ f.η.app S := by
  change 𝟙 _ ≫ (g.η.app (f.Φ.obj S) ≫ f.η.app S) = _
  rw [Category.id_comp]

set_option linter.checkUnivs false in
/-- π-institutions and consequence-preserving comorphisms. The value category
is the existing category of Tarskian entailment relations. See Defs1.5–1.6 and Rem1.7. -/
abbrev PiCoIns := CoDiagram.{u,v} ER.{w}

set_option linter.checkUnivs false in
/-- π-institutions and consequence-preserving morphisms. -/
abbrev PiIns := MorDiagram.{u,v} ER.{w}

/-- Every ordinary institution has a π-institution of semantic consequence.
No adequacy/completeness assumption about a syntactic calculus is used. -/
def semanticPi (A : Inst.{u,v,w,y,z}) : Diagram.{u,v} ER.{w} :=
  ⟨A.Sign, A.I ⋙ Room.semanticFunctor⟩

end Silmaril.Logic.Institution

namespace Silmaril.Logic.Institution

open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Metatheory

universe u v w x y z p q

/-- Postcomposition acts on diagrams and their changes of index category. -/
def CoDiagram.postcompose {C : Type w} [Category.{x} C]
    {D : Type y} [Category.{z} D] (F : C ⥤ D) :
    CoDiagram.{u,v} C ⥤ CoDiagram.{u,v} D where
  obj A := letI := A.cat; ⟨A.Sign, A.I ⋙ F⟩
  map {A B} f :=
    letI := A.cat
    letI := B.cat
    ⟨f.Φ, Functor.whiskerRight f.ρ F ≫ (Functor.associator f.Φ B.I F).hom⟩
  map_id A := by
    refine Diagram.CoHom.ext ?_ ?_
    · rfl
    · simp only [eqToHom_refl, Category.comp_id]
      apply NatTrans.ext
      funext S
      simp
  map_comp f g := by
    refine Diagram.CoHom.ext ?_ ?_
    · rfl
    · simp only [eqToHom_refl, Category.comp_id]
      apply NatTrans.ext
      funext S
      simp

/-- Ordinary institutions are diagrams in rooms, including their actual
comorphisms. This bridge preserves their signature functors. -/
def institutionDiagrams : CoIns.{u,v,w,p,q} ⥤ CoDiagram.{u,v} Room.{w,p,q} where
  obj A := letI := A.cat; ⟨A.Sign, A.I⟩
  map f := ⟨f.Φ, f.ρ⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Forget models but retain the full signature category, sentence translation,
and its proved preservation of semantic consequence. -/
def semanticPiFunctor : CoIns.{u,v,w,p,q} ⥤ PiCoIns.{u,v,w} :=
  institutionDiagrams ⋙ CoDiagram.postcompose Room.semanticFunctor

/-- The morphism-direction version of the same diagram construction. -/
def MorDiagram.postcompose {C : Type w} [Category.{x} C]
    {D : Type y} [Category.{z} D] (F : C ⥤ D) :
    MorDiagram.{u,v} C ⥤ MorDiagram.{u,v} D where
  obj A := letI := A.cat; ⟨A.Sign, A.I ⋙ F⟩
  map {A B} f :=
    letI := A.cat
    letI := B.cat
    ⟨f.Φ, (Functor.associator f.Φ B.I F).inv ≫ Functor.whiskerRight f.η F⟩
  map_id A := by
    refine Diagram.Hom.ext ?_ ?_
    · rfl
    · simp only [eqToHom_refl, Category.id_comp]
      apply NatTrans.ext
      funext S
      simp only [NatTrans.comp_app, Functor.associator_inv_app, Functor.whiskerRight_app,
        MorDiagram.id_app, Category.id_comp]
      exact F.map_id _
  map_comp f g := by
    refine Diagram.Hom.ext ?_ ?_
    · rfl
    · simp only [eqToHom_refl, Category.id_comp]
      apply NatTrans.ext
      funext S
      simp

/-- Institution morphisms also preserve semantic consequence in their backward
sentence direction. No model-expansion hypothesis is needed for preservation. -/
def semanticPiMorphismFunctor : Ins.{u,v,w,p,q} ⥤ PiIns.{u,v,w} where
  obj A := semanticPi A
  map {A B} f :=
    letI := A.cat
    letI := B.cat
    ⟨f.Φ, (Functor.associator f.Φ B.I Room.semanticFunctor).inv ≫
      Functor.whiskerRight f.η Room.semanticFunctor⟩
  map_id A := by
    refine Diagram.Hom.ext ?_ ?_
    · rfl
    · simp only [eqToHom_refl, Category.id_comp]
      apply NatTrans.ext
      funext S
      apply ER.hom_ext
      rfl
  map_comp f g := by
    refine Diagram.Hom.ext ?_ ?_
    · rfl
    · simp only [eqToHom_refl, Category.id_comp]
      apply NatTrans.ext
      funext S
      apply ER.hom_ext
      rfl

end Silmaril.Logic.Institution
