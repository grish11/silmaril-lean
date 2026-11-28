module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Typing.Thms

/-! # Checked removal of redundant unit binders at packed routers -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {X : Syntax.Ty}
variable {Γ R L : List Syntax.Ty}

/-- Insert a literal unit binder with exact weakening of every old variable. -/
def bindUnusedUnit (r : Typed Φ Γ L) : Typed Φ Γ L :=
  ⟨.let₁ .unit (r.val.renameVars Nat.succ),
    .let₁ .unit (r.property.renameVars (LambdaSSA.Ren.wk Γ (.unit : Syntax.Ty)))⟩

/-- Each new binder weakens the whole existing stack, including its router. -/
def bindUnusedUnits : Nat → Typed Φ Γ L → Typed Φ Γ L
  | 0, r => r
  | n + 1, r => bindUnusedUnit (bindUnusedUnits n r)

/-- Re-emit the readback with the selected stack depths at its packed routers. -/
def Readback.withRouterUnitDepths (w : Readback Φ X R L) (depths : Fin R.length → Nat) : Typed Φ [X] L :=
  let blocks (i : Fin R.length) : Typed Φ (R.get i :: [X]) (R ++ L) :=
    bind (w.producer i).typed (bindUnusedUnits (depths i) (route R L))
  ⟨nativeFeedback w.entry blocks, nativeFeedback_hasType w.entry blocks⟩

/-- Re-emit with zero or one redundant binder at each router. -/
def Readback.withRouterUnits (w : Readback Φ X R L) (units : Fin R.length → Bool) : Typed Φ [X] L :=
  w.withRouterUnitDepths (fun i => if units i then 1 else 0)

/-- Count the leading literal-unit binders in a router candidate. -/
def leadingUnitBinders : LambdaSSA.Region Φ → Nat
  | .let₁ .unit body => leadingUnitBinders body + 1
  | _ => 0

/-- Count the candidate stack only at the continuation of the packed
producer. The subsequent exact comparison validates its weakening. -/
def routerUnitDepth (r : LambdaSSA.Region Φ) (i : Nat) : Nat :=
  match r with
  | .cfg _ n blocks =>
    if bound : i < n then
      match blocks ⟨i, bound⟩ with
      | .cfg _ 1 next => leadingUnitBinders (next 0)
      | _ => 0
    else 0
  | _ => 0

/-- Detect whether there is any leading literal-unit binder at the router. -/
def hasRouterUnit (r : LambdaSSA.Region Φ) (i : Nat) : Bool :=
  routerUnitDepth r i != 0

variable [DecidableEq Φ]

/-- The re-emitted entry, producers, and possibly padded routers must match
the original syntax exactly. Only the matched padding is removed. -/
def normalizeRouterUnits (R : List Syntax.Ty) (raw : Typed Φ [X] L) : Option (Typed Φ [X] L) := do
  let w ← propose R L raw.val
  let depths := fun i : Fin R.length => routerUnitDepth raw.val i
  if sameRegion raw.val (w.withRouterUnitDepths depths).val then some w.typed else none

/-- Run the existing exact recognizer on the checked normal form. -/
def recognizeRouterUnits (R : List Syntax.Ty) (raw : Typed Φ [X] L) : Option (Readback Φ X R L) :=
  (normalizeRouterUnits R raw).bind (recognize R)

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native
