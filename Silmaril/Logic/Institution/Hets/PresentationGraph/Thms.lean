module

public import Silmaril.Logic.Institution.Hets.PresentationGraph.Defs

@[expose] public section
namespace Silmaril.Logic.Institution.Hets.PresentationGraph
open CategoryTheory Silmaril.Logic.Institution
universe u v w m n
variable {Sign : Type u} [Category.{v} Sign] (I : Sign ⥤ Room.{w,m,n})

/-- The recursively defined Hets model class is exactly the presentation models. -/
theorem models_iff (P : Presentation I) (M : (I.obj P.sig).Mod) :
    M ∈ (ofPresentation I P).models () ↔ ∀ e ∈ P.axioms, (I.obj P.sig).Sat M e := by
  exact (DevGraph.mem_models_iff (ofPresentation I P) () M).trans
    (by
      constructor
      · exact fun h => h.1
      · intro h
        refine ⟨h, ?_, ?_, ?_⟩
        all_goals intro K σ member; exact False.elim member)

/-- Hets semantic consequences coincide with the presentation consequences. -/
theorem entails_iff (P : Presentation I) (e : (I.obj P.sig).Sen) :
    (∀ M ∈ (ofPresentation I P).models (), (I.obj P.sig).Sat M e) ↔
      (I.obj P.sig).Entails P.axioms e := by
  constructor
  · intro h M member
    exact h M ((models_iff I P M).2 member)
  · intro h M member
    exact h M ((models_iff I P M).1 member)

end Silmaril.Logic.Institution.Hets.PresentationGraph
