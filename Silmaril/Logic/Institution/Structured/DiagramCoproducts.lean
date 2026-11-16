module

public import Silmaril.Logic.Institution.Pi.Defs
public import Mathlib.CategoryTheory.Sigma.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products

set_option backward.isDefEq.respectTransparency false

@[expose] public section
namespace Silmaril.Logic.Institution.CoDiagram
open CategoryTheory CategoryTheory.Limits
universe u w x
variable {C : Type w} [Category.{x} C] {ι : Type u}

/-- Disjoint union of diagram shapes and their original values. No coproduct
in the value category is required (Durán–Meseguer, Lemma 3.5). -/
def coproduct (D : ι → CoDiagram.{u,u} C) : CoDiagram.{u,u} C :=
  ⟨(i : ι) × (D i).Sign, Sigma.desc (fun i => (D i).I)⟩

/-- Include one diagram as its own component of the disjoint union. -/
def coproductInclusion (D : ι → CoDiagram.{u,u} C) (i : ι) : D i ⟶ coproduct D where
  Φ := Sigma.incl (C := fun i => (D i).Sign) i
  ρ := { app := fun _ => 𝟙 _ }

/-- Assemble a family of diagram maps on the disjoint union. -/
def coproductDesc (D : ι → CoDiagram.{u,u} C) {E : CoDiagram.{u,u} C}
    (f : ∀ i, D i ⟶ E) : coproduct D ⟶ E where
  Φ := Sigma.desc (fun i => (f i).Φ)
  ρ := {
    app := fun node => (f node.1).ρ.app node.2
    naturality := by
      rintro ⟨i, a⟩ ⟨_, b⟩ ⟨g⟩
      exact (f i).ρ.naturality g }

@[simp] theorem coproductInclusion_desc (D : ι → CoDiagram.{u,u} C) {E : CoDiagram.{u,u} C}
    (f : ∀ i, D i ⟶ E) (i : ι) :
    coproductInclusion D i ≫ coproductDesc D f = f i := by
  apply Diagram.CoHom.ext (f := coproductInclusion D i ≫ coproductDesc D f) (g := f i) rfl
  simp only [eqToHom_refl, Category.comp_id]
  apply NatTrans.ext
  funext node
  simp [CoDiagram.comp_app, coproductInclusion, coproductDesc]

/-- A diagram map is determined by its restrictions to the disjoint components. -/
theorem coproduct_hom_ext (D : ι → CoDiagram.{u,u} C) {E : CoDiagram.{u,u} C}
    {f g : coproduct D ⟶ E}
    (h : ∀ i, coproductInclusion D i ≫ f = coproductInclusion D i ≫ g) : f = g := by
  have hobj : ∀ node, f.Φ.obj node = g.Φ.obj node := by
    rintro ⟨i, node⟩
    exact congrArg (fun k => k.Φ.obj node) (h i)
  have hΦ : f.Φ = g.Φ := by
    refine Functor.ext hobj ?_
    rintro ⟨i, a⟩ ⟨_, b⟩ ⟨k⟩
    exact Functor.congr_hom (congrArg (fun f => f.Φ) (h i)) k
  have hr (i : ι) (node : (D i).Sign) :
      HEq ((coproductInclusion D i ≫ f).ρ.app node)
        ((coproductInclusion D i ≫ g).ρ.app node) := by
    have hi := congrArg (fun k => (⟨k.Φ.obj node, k.ρ.app node⟩ :
      (n : E.Sign) × ((D i).I.obj node ⟶ E.I.obj n))) (h i)
    exact (Sigma.mk.inj hi).2
  cases f with
  | mk F ρf =>
    show (⟨F, ρf⟩ : Diagram.CoHom (coproduct D) E) = g
    cases g with
    | mk G ρg =>
      show (⟨F, ρf⟩ : Diagram.CoHom (coproduct D) E) = ⟨G, ρg⟩
      change F = G at hΦ
      cases hΦ
      apply congrArg (fun ρ => (⟨F, ρ⟩ : Diagram.CoHom (coproduct D) E))
      apply NatTrans.ext
      funext node
      rcases node with ⟨i, node⟩
      have hi := hr i node
      simpa [CoDiagram.comp_app, coproductInclusion] using eq_of_heq hi

/-- The universal cocone of the disjoint-union diagram. -/
def coproductCofan (D : ι → CoDiagram.{u,u} C) : Cofan D :=
  Cofan.mk (coproduct D) (coproductInclusion D)

/-- The actual coproduct universal property, including uniqueness of diagram maps. -/
def coproductIsColimit (D : ι → CoDiagram.{u,u} C) : IsColimit (coproductCofan D) :=
  Cofan.IsColimit.mk _ (fun s => coproductDesc D s.inj)
    (fun _ i => coproductInclusion_desc D _ i)
    (fun s _m hm => coproduct_hom_ext D (fun i => (hm i).trans (coproductInclusion_desc D s.inj i).symm))

/-- All small coproducts exist in the varying-shape diagram category. -/
instance hasCoproducts : HasCoproducts.{u} (CoDiagram.{u,u} C) :=
  hasCoproducts_of_colimit_cofans coproductCofan coproductIsColimit

end Silmaril.Logic.Institution.CoDiagram
