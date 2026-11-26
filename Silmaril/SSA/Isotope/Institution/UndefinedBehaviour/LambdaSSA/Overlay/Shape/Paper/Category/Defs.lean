module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Thms
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Thms
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Descent.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Defs

/-! # The shaped observation arrow of a guarded Paper continuation -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Paper

open CategoryTheory

universe u v w x

variable {Φ : Type u} {κ : Type v} [HasTy Φ (Ty κ)] {Γ L K : List (Ty κ)}

/-- Interpret a Paper continuation at a fixed shaped capture environment.
Each chosen input label binds its own typed payload. -/
noncomputable def interpretHom (M : Shape.Model.{u,v,w,x} Φ Γ)
    (f : LambdaSSA.Region.Paper.Hom (Φ := Φ) Γ L K) :
    (⟨L⟩ : Shape.Category.Interface M.raw.α M.raw.σ M.atomType) ⟶ ⟨K⟩ where
  run i a s := denote f i (M.extend a.property) s
  returnsTyped i a s := Quotient.inductionOn f
    (fun r => Shape.returns_typed (.native (Shape.Continuation.familyMember r i)) (M.extend a.property) s)

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Paper
