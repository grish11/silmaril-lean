module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.Normalize.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.Normalize.Soundness

/-! # Shaped soundness of checked packed-router normalization -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native

open Syntax (Primitives emptyBindings Bindings.push model)
open LambdaSSA.Region (SubstitutionEquiv)

universe u v w

variable {Φ : Type u} [HasTy Φ Syntax.Ty]
variable {Γ R L : List Syntax.Ty} {X : Syntax.Ty}
variable {captures seeds results states : Nat}

/-- Substituting unit after exact weakening recovers the original region. -/
theorem bindUnusedUnit_equiv (r : Typed Φ Γ L) :
    SubstitutionEquiv Γ (bindUnusedUnit r).val r.val L :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native.Normalize.bindUnusedUnit_equiv r

variable [DecidableEq Φ]

/-- Successful normalization supplies an installed native substitution
equation at the original exact interface. -/
theorem normalizeRouterUnits_equiv {raw normal : Typed Φ [X] L}
    (normalized : normalizeRouterUnits R raw = some normal) :
    SubstitutionEquiv [X] raw.val normal.val L :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native.Normalize.normalize_equiv normalized

/-- The normalization preserves complete shaped observations, with the
original entry, states, and ordered exit labels. -/
theorem normalizeRouterUnits_denote {raw normal : Typed Φ [X] L}
    (normalized : normalizeRouterUnits R raw = some normal)
    (M : Shape.Model.{u,0,v,w} Φ [X]) (s : M.raw.σ) :
    Shape.denote (.native raw) M s = Shape.denote (.native normal) M s :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native.Normalize.normalize_denote
    normalized M s

/-- The unchanged finite scan classifies the original accepted CFG. -/
theorem classify_recognizedRouterUnits {raw : Typed Φ [X] L} {readback : Readback Φ X R L}
    (accepted : recognizeRouterUnits R raw = some readback) (C : Codes X R L captures seeds results)
    (prim : Primitives Φ states) (c : Fin captures) (s : Fin states) :
    Shape.denote (.native raw) (model prim (emptyBindings.push (C.capture c))) s =
      (readback.execute C prim c s).routed C.carrier :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native.Normalize.classify_routerUnits
    accepted C prim c s

/-- Checked normalization and exact readback retain the existing comparison
of the original native CFGs at every coded start. -/
theorem check_recognizedRouterUnits_iff {raw target : Typed Φ [X] L}
    {left right : Readback Φ X R L}
    (hl : recognizeRouterUnits R raw = some left) (hr : recognizeRouterUnits R target = some right)
    (C : Codes X R L captures seeds results) (prim : Primitives Φ states) :
    check left right C prim = true ↔ ∀ (c : Fin captures) (s : Fin states),
      let M := model prim (emptyBindings.push (C.capture c))
      Shape.denote (.native raw) M s ≤ Shape.denote (.native target) M s :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native.Normalize.check_routerUnits_iff
    hl hr C prim

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native
