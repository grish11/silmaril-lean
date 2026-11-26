module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Category.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Category.Representatives
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Behaviour

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Category

open CategoryTheory
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Paper (interpretHom)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Continuation (familyMember)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category (Interface Arrow arrow_ext comp_run id_run)
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category (bind_congr)

universe u v w x

variable {Φ : Type u} {κ : Type v} [HasTy Φ (Ty κ)] {Γ L K P : List (Ty κ)}
variable (M : Shape.Model.{u,v,w,x} Φ Γ)

theorem interpretHom_id :
    interpretHom M (Region.Paper.Hom.identity Γ L) =
      𝟙 (⟨L⟩ : Interface M.raw.α M.raw.σ M.atomType) := by
  apply arrow_ext
  intro i a s
  rw [id_run]
  exact congrArg WithTop.some (identity_outcomes i M.raw a.val s)

theorem interpretHom_comp (f : Region.Paper.Hom (Φ := Φ) Γ L K)
    (g : Region.Paper.Hom (Φ := Φ) Γ K P) :
    interpretHom M (f.compose g) = interpretHom M f ≫ interpretHom M g := by
  induction f, g using Quotient.inductionOn₂ with
  | h f g =>
    apply arrow_ext
    intro i a s
    rw [comp_run]
    let f' : Arrow (⟨L⟩ : Interface M.raw.α M.raw.σ M.atomType) ⟨K⟩ :=
      interpretHom M (Quotient.mk _ f)
    let g' : Arrow (⟨K⟩ : Interface M.raw.α M.raw.σ M.atomType) ⟨P⟩ :=
      interpretHom M (Quotient.mk _ g)
    change (↑(nativeOutcomes (familyMember (f.compose g) i) (extendModel M.raw a.val) s) :
      Behaviour P.length M.raw.α M.raw.σ) = (f'.run i a s).bind g'.total
    rw [compose_outcomes]
    refine (Behaviour.coe_bind _ _).symm.trans (bind_congr (p := f'.run i a s) ?_)
    intro j b t reached
    exact (g'.total_typed j ⟨b, f'.returnsTyped i a s reached⟩ t).symm

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Category
