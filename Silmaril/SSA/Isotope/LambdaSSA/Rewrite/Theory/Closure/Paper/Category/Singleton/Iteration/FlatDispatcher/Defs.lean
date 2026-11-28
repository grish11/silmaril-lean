module

public import Silmaril.SSA.Isotope.LambdaSSA.Flat.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Blocks.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Roundtrip.Labels.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Singleton.Defs

/-! # The packed one-step dispatcher of a typed flat CFG -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.FiniteCFG

open CategoryTheory CategoryTheory.Limits
open Region Region.ContinuationContext
open Region.Paper.TypeCategory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {blocks exits : Nat} {R : Fin blocks → τ} {E : Fin exits → τ}

local notation "Ctx" => ContinuationContext Φ ([] : VCtx τ)

/-- Send internal labels to recurrence and external labels to the outward sum.
The positional CFG convention lists internal labels first. -/
def routeExit (blocks i : Nat) : Region Φ :=
  if i < blocks then .br 0 (.inr (packedExitArg i (.var 0)))
  else .br 0 (.inl (packedExitArg (i - blocks) (.var 0)))

/-- The runtime tags preserve the original payload and distinguish recurrence
from an outward exit. -/
def routeValue {α : Type u} (blocks i : Nat) (value : Value α) : Value α :=
  if i < blocks then .inr (packedExitValue i value)
  else .inl (packedExitValue (i - blocks) value)

/-- Route a scoped flat region's guarded branches to a single tagged exit. -/
def routedFlat {labels n : Nat} (blocks : Nat) (r : Flat Φ labels n) : Region Φ :=
  r.erase.bindBranchArguments.lsubst (routeExit blocks)

/-- A guarded native arrow packs outgoing labels into the exact exit-or-state sum. -/
def routeFamily (R E : LCtx τ) (Γ : VCtx τ := []) :
    ContinuationFamily (Φ := Φ) Γ (R ++ E) [Silmaril.coprod (packedExitType E) (packedExitType R)] :=
  ⟨routeExit R.length, by
    intro i A hi
    by_cases h : i < R.length
    · rw [routeExit, ite_eq_left h]
      have hi' : At R i A := (List.getElem?_append_left h).symm.trans hi
      cases packExits_valueFamily (Φ := Φ) Γ R hi' with
      | br ho hv =>
        cases Option.some.inj ho
        exact .br rfl (.inr hv)
    · rw [routeExit, ite_eq_right h]
      have hi' : At E (i - R.length) A :=
        (List.getElem?_append_right (Nat.le_of_not_gt h)).symm.trans hi
      cases packExits_valueFamily (Φ := Φ) Γ E hi' with
      | br ho hv =>
        cases Option.some.inj ho
        exact .br rfl (.inl hv)⟩

/-- The native continuation arrow with one guarded representative for each
actual flat block. Binding the branch arguments evaluates them once before
the outgoing labels are routed. -/
def blockFamily {n : Nat} {β : BoundCtx τ n} {g : FiniteCFG Φ blocks exits n}
    (hg : HasType β R E g) :
    ContinuationFamily (Φ := Φ) β.toList (List.ofFn R) (List.ofFn R ++ List.ofFn E) :=
  ContinuationFamily.ofTyped (σ := fun i => if h : i < blocks then (g.block ⟨i, h⟩).erase else labelId i) (by
    intro i A hi
    have h : i < blocks := by simpa using (List.getElem?_eq_some_iff.mp hi).1
    simp only [dite_eq_left h]
    have he : R ⟨i, h⟩ = A := Option.some.inj ((SSA.FiniteSum.at_ofFn R ⟨i, h⟩).symm.trans hi)
    simpa [BoundCtx.toList, he] using (hg.block ⟨i, h⟩).erase)

/-- The selected block with its original label interface and guarded branches. -/
theorem blockValueBranches {g : FiniteCFG Φ blocks exits 0} (hg : HasType .nil R E g) (i : Fin blocks) :
    ValueBranches [R i] (g.block i).erase.bindBranchArguments (List.ofFn R ++ List.ofFn E) := by
  apply Region.HasType.bindBranchArguments
  simpa [BoundCtx.toList] using (hg.block i).erase

/-- The original label at a fixed payload type, before packing. -/
def selectLabel {L : LCtx τ} {i : Nat} {A : τ} (hi : At L i A) :
    (single A : Ctx) ⟶ (⟨L⟩ : Ctx) :=
  singletonToHom (r := labelId i) (.br hi (.var (i := 0) rfl))

/-- Encode an original label family as one singleton sum of its payload types. -/
def packLabels (L : LCtx τ) : (⟨L⟩ : Ctx) ⟶ single (packedExitType L) :=
  ContinuationFamily.toHom ⟨_, packExits_valueFamily [] L⟩

/-- Decode the packed input by the original label order. -/
def unpackLabels (L : LCtx τ) : (single (packedExitType L) : Ctx) ⟶ (⟨L⟩ : Ctx) :=
  ContinuationFamily.toHom ⟨_, unpackExits_valueFamily [] L⟩

/-- The packed block injection, obtained by tagging the selected native label. -/
def packedBlockIn (i : Fin blocks) :
    ofType (Φ := Φ) (R i) ⟶ ofType (packedExitType (List.ofFn R)) :=
  InducedCategory.homMk (Region.Paper.fromNative.map
    (selectLabel (SSA.FiniteSum.at_ofFn R i) ≫ packLabels (List.ofFn R)))

/-- Execute one block and tag its outgoing label. -/
noncomputable def blockStep {g : FiniteCFG Φ blocks exits 0}
    (hg : HasType .nil R E g) (i : Fin blocks) :
    ofType (Φ := Φ) (R i) ⟶ ofType (packedExitType (List.ofFn E)) ⨿ ofType (packedExitType (List.ofFn R)) :=
  InducedCategory.homMk (Region.Paper.fromNative.map
    (singletonToHom (Y := (⟨List.ofFn R ++ List.ofFn E⟩ : Ctx)) (blockValueBranches hg i) ≫
      (routeFamily (Φ := Φ) (List.ofFn R) (List.ofFn E)).toHom)) ≫
    (sumIso (packedExitType (List.ofFn E)) (packedExitType (List.ofFn R))).hom

/-- Decode the incoming block label, execute exactly one block, and route its
result to either the packed outward interface or the packed recurrence state. -/
noncomputable def packedDispatcher {g : FiniteCFG Φ blocks exits 0}
    (hg : HasType .nil R E g) :
    ofType (Φ := Φ) (packedExitType (List.ofFn R)) ⟶
      ofType (packedExitType (List.ofFn E)) ⨿ ofType (packedExitType (List.ofFn R)) :=
  InducedCategory.homMk (Region.Paper.fromNative.map
    (unpackLabels (List.ofFn R) ≫ (blockFamily hg).toHom ≫
      (routeFamily (Φ := Φ) (List.ofFn R) (List.ofFn E)).toHom)) ≫
    (sumIso (packedExitType (List.ofFn E)) (packedExitType (List.ofFn R))).hom

end Silmaril.Isotope.LambdaSSA.FiniteCFG
