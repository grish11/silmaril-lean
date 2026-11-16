module

public import Silmaril.Logic.Institution.Structured.Constraints.Defs

set_option backward.isDefEq.respectTransparency false

@[expose] public section
namespace Silmaril.Logic.Institution.Structured.Constraints
open CategoryTheory Silmaril.Logic.Institution
universe u v s p q
variable {Sign : Type u} [Category.{v} Sign] (I : Sign ⥤ Room.{s,p,q})

/-- A freeness constraint retains both the theory map and the extra signature
map bringing the model into context (Durán–Meseguer 1999, Definition 4.14). -/
structure Constraint (S : Sign) where
  source : Spec I
  target : Spec I
  theoryMap : source ⟶ target
  context : target.sig ⟶ S

/-- Translate only the context map, retaining the same theory map. -/
def translate {S T : Sign} (f : S ⟶ T) (c : Constraint I S) : Constraint I T :=
  { c with context := c.context ≫ f }

/-- Satisfaction uses the pointwise universal free-extension condition.
It is meaningful without choosing a left adjoint for every theory map. -/
def Sat {S : Sign} (M : (I.obj S).Mod) (c : Constraint I S) : Prop :=
  ∃ h : Theory.modelsProperty c.target.axioms ((I.map c.context).mod.obj M),
    FreeAt (SemanticModels.reduct I c.theoryMap) ⟨(I.map c.context).mod.obj M, h⟩

theorem translate_id {S : Sign} (c : Constraint I S) : translate I (𝟙 S) c = c := by
  cases c
  simp only [translate, Category.comp_id]

theorem translate_comp {S T U : Sign} (f : S ⟶ T) (g : T ⟶ U) (c : Constraint I S) :
    translate I (f ≫ g) c = translate I g (translate I f c) := by
  cases c
  simp only [translate, Category.assoc]

/-- The satisfaction condition for actual freeness constraints. -/
theorem satisfaction {S T : Sign} (f : S ⟶ T) (M : (I.obj T).Mod) (c : Constraint I S) :
    Sat I M (translate I f c) ↔ Sat I ((I.map f).mod.obj M) c := by
  simp only [Sat, translate, I.map_comp]
  rfl

/-- With a chosen adjunction, satisfaction is precisely the paper's
satisfying-target-model plus invertible-counit condition. -/
theorem sat_iff_counit_isIso {S : Sign} (M : (I.obj S).Mod) (c : Constraint I S)
    {L : SemanticModels.Models I c.source ⥤ SemanticModels.Models I c.target}
    (adj : L ⊣ SemanticModels.reduct I c.theoryMap) :
    Sat I M c ↔ ∃ h : Theory.modelsProperty c.target.axioms ((I.map c.context).mod.obj M),
      IsIso (adj.counit.app ⟨(I.map c.context).mod.obj M, h⟩) :=
  exists_congr (fun _ => freeAt_iff_counit_isIso adj _)

/-- Original sentences and freeness constraints share the original signatures
and model categories. -/
def room (S : Sign) : Room.{max u v s,p,q} :=
  ⟨(I.obj S).Sen ⊕ Constraint I S, (I.obj S).Mod,
    fun M φ => Sum.elim ((I.obj S).Sat M) (Sat I M) φ⟩

/-- Translate original sentences normally and constraints by context composition. -/
def corridor {S T : Sign} (f : S ⟶ T) : room I S ⟶ room I T :=
  ⟨Sum.map (I.map f).sen (translate I f), (I.map f).mod, by
    intro M φ
    cases φ with
    | inl φ => exact (I.map f).sat M φ
    | inr c => exact satisfaction I f M c⟩

theorem corridor_id (S : Sign) : corridor I (𝟙 S) = 𝟙 (room I S) := by
  apply Room.hom_ext
  · funext φ
    cases φ with
    | inl φ => simp only [corridor, I.map_id]; rfl
    | inr c => exact congrArg Sum.inr (translate_id I c)
  · change (I.map (𝟙 S)).mod = 𝟭 _
    rw [I.map_id]
    rfl

theorem corridor_comp {S T U : Sign} (f : S ⟶ T) (g : T ⟶ U) :
    corridor I (f ≫ g) = corridor I f ≫ corridor I g := by
  apply Room.hom_ext
  · funext φ
    cases φ with
    | inl φ => simp only [corridor, I.map_comp]; rfl
    | inr c => exact congrArg Sum.inr (translate_comp I f g c)
  · change (I.map (f ≫ g)).mod = (I.map g).mod ⋙ (I.map f).mod
    rw [I.map_comp]
    rfl

/-- The actual constraint institution `C(I)`, with the same signatures and
model functor as `I` (Definition 4.14 and its following construction). -/
def institution : Sign ⥤ Room.{max u v s,p,q} where
  obj := room I
  map := corridor I
  map_id := corridor_id I
  map_comp := corridor_comp I

/-- Original sentences embed into the constraint institution. -/
def inclusion (I : Sign ⥤ Room.{max u v s,p,q}) : I ⟶ institution I where
  app := fun S => ⟨Sum.inl, 𝟭 (I.obj S).Mod, fun _ _ => Iff.rfl⟩
  naturality := by
    intro S T f
    apply Room.hom_ext
    · rfl
    · change (I.map f).mod ⋙ 𝟭 _ = 𝟭 _ ⋙ (I.map f).mod
      rw [Functor.comp_id, Functor.id_comp]

/-- Every satisfying target model satisfies the identity freeness constraint;
this supplies populated cases independent of any global liberality assumption. -/
theorem freeAt_identity (T : Spec I) (M : SemanticModels.Models I T) :
    FreeAt (SemanticModels.reduct I (𝟙 T)) M := by
  have hred : SemanticModels.reduct I (𝟙 T) = 𝟭 _ :=
    congrArg (fun c => c.mod) (SemanticModels.corridor_id I T)
  rw [hred]
  intro N
  exact Function.bijective_id

end Silmaril.Logic.Institution.Structured.Constraints
