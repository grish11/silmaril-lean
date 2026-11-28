module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.Normalize.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Defs
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Continuation.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.Syntax

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native.Normalize

open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.Region (SubstitutionEquiv substVars_renameVars substVars_var renameVars_renameLabels)
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.Syntax
  (Primitives emptyBindings Bindings.push model)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent (Codes)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native (sameRegion_eq)

universe u v w

variable {Φ : Type u} [HasTy Φ (Silmaril.Ty Empty)]
variable {Γ R L : List (Silmaril.Ty Empty)} {X A : Silmaril.Ty Empty}
variable {captures seeds results states : Nat}

theorem bindUnusedUnit_equiv (r : Typed Φ Γ L) :
    SubstitutionEquiv Γ (bindUnusedUnit r).val r.val L := by
  have drop : LambdaSSA.Tm.singleSubst (.unit : LambdaSSA.Tm Φ) ∘ Nat.succ = LambdaSSA.Tm.var := rfl
  simpa only [bindUnusedUnit, substVars_renameVars, drop, substVars_var] using
    (SubstitutionEquiv.letValue .unit (r.property.renameVars (LambdaSSA.Ren.wk Γ (.unit : Silmaril.Ty Empty))))

private theorem bind_unit_equiv (p : Typed Φ Γ [A]) (k : Typed Φ (A :: Γ) L) :
    SubstitutionEquiv Γ (bind p (bindUnusedUnit k)).val (bind p k).val L := by
  have keepLabel : SSA.Ren [A] ([A] ++ L) id := by
    intro i B typed
    exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp typed).1).trans typed
  have entryTyped : p.val.HasType Γ (A :: L) := by
    simpa only [LambdaSSA.Region.renameLabels_id, List.cons_append, List.nil_append] using p.property.renameLabels keepLabel
  refine .cfg (fun _ : Fin 1 => A) (.base (.refl entryTyped)) ?_
  intro i
  obtain rfl := Fin.eq_zero i
  have shift : SSA.Ren L (A :: L) (1 + ·) := by
    simpa only [Nat.one_add] using (SSA.Ren.wk L A)
  change SubstitutionEquiv (A :: Γ)
    (.let₁ .unit ((k.val.renameVars Nat.succ).renameLabels (1 + ·)))
    (k.val.renameLabels (1 + ·)) (A :: L)
  rw [← renameVars_renameLabels]
  exact bindUnusedUnit_equiv ⟨_, k.property.renameLabels shift⟩

private theorem bind_units_equiv (p : Typed Φ Γ [A]) (k : Typed Φ (A :: Γ) L) (n : Nat) :
    SubstitutionEquiv Γ (bind p (bindUnusedUnits n k)).val (bind p k).val L := by
  induction n with
  | zero => exact .base (.refl (bind p k).property)
  | succ n ih => exact (bind_unit_equiv p (bindUnusedUnits n k)).trans ih

private theorem withRouterUnitDepths_equiv (w : Readback Φ X R L) (depths : Fin R.length → Nat) :
    SubstitutionEquiv [X] (w.withRouterUnitDepths depths).val w.typed.val L := by
  refine .cfg (List.get R) ?_ ?_
  · simpa only [List.ofFn_get] using
      (SubstitutionEquiv.base (.refl w.entry.property))
  · intro i
    simpa only [List.ofFn_get, Readback.routed] using bind_units_equiv (w.producer i).typed (route R L) (depths i)

variable [DecidableEq Φ]

theorem normalize_equiv {raw normal : Typed Φ [X] L}
    (normalized : normalizeRouterUnits R raw = some normal) :
    SubstitutionEquiv [X] raw.val normal.val L := by
  obtain ⟨candidate, _, checked⟩ := Option.bind_eq_some_iff.mp normalized
  dsimp only at checked
  split at checked
  · rename_i same
    obtain rfl := Option.some.inj checked
    rw [sameRegion_eq same]
    exact withRouterUnitDepths_equiv candidate _
  · cases checked

theorem normalize_denote {raw normal : Typed Φ [X] L}
    (normalized : normalizeRouterUnits R raw = some normal)
    (M : Shape.Model.{u,0,v,w} Φ [X]) (s : M.raw.σ) :
    Shape.denote (.native raw) M s = Shape.denote (.native normal) M s :=
  Shape.Continuation.substitutionEquiv_denote (normalize_equiv normalized) M s

theorem classify_routerUnits {raw : Typed Φ [X] L} {readback : Readback Φ X R L}
    (accepted : recognizeRouterUnits R raw = some readback) (C : Codes X R L captures seeds results)
    (prim : Primitives Φ states) (c : Fin captures) (s : Fin states) :
    Shape.denote (.native raw) (model prim (emptyBindings.push (C.capture c))) s =
      (readback.execute C prim c s).routed C.carrier := by
  obtain ⟨_, normalized, exactReadback⟩ := Option.bind_eq_some_iff.mp accepted
  exact (normalize_denote normalized (model prim (emptyBindings.push (C.capture c))) s).trans
    (classify_recognized exactReadback C prim c s)

theorem check_routerUnits_iff {raw target : Typed Φ [X] L} {left right : Readback Φ X R L}
    (hl : recognizeRouterUnits R raw = some left) (hr : recognizeRouterUnits R target = some right)
    (C : Codes X R L captures seeds results) (prim : Primitives Φ states) :
    check left right C prim = true ↔ ∀ (c : Fin captures) (s : Fin states),
      let M := model prim (emptyBindings.push (C.capture c))
      Shape.denote (.native raw) M s ≤ Shape.denote (.native target) M s := by
  obtain ⟨_, normalizeLeft, exactLeft⟩ := Option.bind_eq_some_iff.mp hl
  obtain ⟨_, normalizeRight, exactRight⟩ := Option.bind_eq_some_iff.mp hr
  rw [check_recognized_iff exactLeft exactRight C prim]
  refine forall_congr' fun c => forall_congr' fun s => ?_
  dsimp only
  rw [normalize_denote normalizeLeft, normalize_denote normalizeRight]

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native.Normalize
