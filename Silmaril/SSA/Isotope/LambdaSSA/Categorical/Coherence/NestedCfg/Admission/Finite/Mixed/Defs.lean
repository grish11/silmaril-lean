module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Admission.Finite.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Trim.Check.Defs

/-! # Written admission for one nested left-case row and finite ordinary rows -/

@[expose] public section

universe v

namespace Silmaril.Isotope.LambdaSSA.NestedAdmission.Finite.Mixed

open Semantics.Categorical (CfgRestriction)

variable {Φ : Type v} [HasTy Φ (Ty Empty)]

/-- Compact label zero is the nested row. The ordinary local operands and
actual exits carry their payloads without a tag change. -/
def layout (A : Ty Empty) (suffix : LCtx (Ty Empty)) : RouteLayout Empty :=
  (A, some .inl) :: suffix.map fun T => (T, none)

/-- Only the nested row changes its input type in the common dispatcher. -/
def stateTypes {q : Nat} (A : Ty Empty) (ordinary : Fin q → Ty Empty) : Fin (q + 1) → Ty Empty :=
  Fin.cases A ordinary

/-- Present the selected row to the existing inner checker. Its interface
includes all ordinary outer slots before the actual outward exits. -/
def nestedShell {q o : Nat} (c : CfgRestriction Φ o) (keep : Fin (q + 1) ↪ Fin o) : Region Φ :=
  .cfg c.entry 1 (fun _ => c.rows (keep 0))

structure Plan (Φ : Type v) (q o m n : Nat) where
  outer : CfgRestriction Φ o
  inner : Finite.Plan Φ m n
  commonOrdinary : Fin q → Region Φ

def Plan.commonRows {q o m n : Nat} (p : Plan Φ q o m n) : Fin (q + 1) → Region Φ :=
  Fin.cases p.inner.commonInner p.commonOrdinary

/-- An ordinary type is initially anchored when the checked inner entry or
one of its anchored retained rows sends a synthesizing outward operand to it. -/
def Plan.nestedAnchor {q o m n : Nat} (p : Plan Φ q o m n) (i : Fin q) : Bool :=
  let target := m + i.succ.val
  branchesTo target p.inner.commonEntry ||
    (List.finRange m).any fun j => branchesTo target (p.inner.commonRows j)

/-- Propagate the initial anchors through the written ordinary transfers. -/
def Plan.anchors {q o m n : Nat} (p : Plan Φ q o m n) (depth : Nat) : List (Fin q) :=
  anchorWorklist p.nestedAnchor (fun j i => branchesTo i.succ.val (p.commonOrdinary j)) depth

/-- The outer mask may put the nested row at any written index. The entry
must inject left at that row. Its selected arm must pass finite inner
admission. All other retained rows must pass the exact branch/case checker,
and every ordinary input must be anchored by a bounded written path. -/
def check? {q o k n : Nat} (outerKeep : Fin (q + 1) ↪ Fin (o + 1))
    (innerKeep : Fin (k + 1) ↪ Fin (n + 1)) (innerTypes : Fin (k + 1) → Ty Empty)
    (ordinary : Fin q → Ty Empty) (r : Region Φ) (exitTypes : LCtx (Ty Empty) := exits) :
    Option (Plan Φ q (o + 1) (k + 1) (n + 1)) :=
  (CfgRestriction.check? outerKeep exitTypes.length r).bind fun outer =>
  let suffix := List.ofFn ordinary ++ exitTypes
  (Finite.check? innerKeep innerTypes (nestedShell outer outerKeep) suffix).bind fun inner =>
  (Region.checkFamily q (fun i =>
    (outer.rows (outerKeep i.succ)).checkRoutes? (layout inner.payload suffix) [ordinary i])).bind fun rows =>
  let p : Plan Φ q (o + 1) (k + 1) (n + 1) := ⟨outer, inner, rows⟩
  if (List.finRange q).all (fun i => (p.anchors q).contains i) then some p else none

def compare? {q o k n : Nat} (outerKeep : Fin (q + 1) ↪ Fin (o + 1))
    (innerKeep : Fin (k + 1) ↪ Fin (n + 1)) (innerTypes : Fin (k + 1) → Ty Empty)
    (ordinary : Fin q → Ty Empty) (r : Region Φ) (exitTypes : LCtx (Ty Empty) := exits) : Comparison :=
  if (check? outerKeep innerKeep innerTypes ordinary r exitTypes).isSome then .certified else .unknown

/-- The successful restrictions, exact branch checks and computed anchors. -/
structure Plan.Valid {q o k n : Nat} (p : Plan Φ q (o + 1) (k + 1) (n + 1))
    (outerKeep : Fin (q + 1) ↪ Fin (o + 1)) (innerKeep : Fin (k + 1) ↪ Fin (n + 1))
    (innerTypes : Fin (k + 1) → Ty Empty) (ordinary : Fin q → Ty Empty)
    (r : Region Φ) (exitTypes : LCtx (Ty Empty)) : Prop where
  outer : p.outer.Valid outerKeep exitTypes.length r
  inner : p.inner.Valid innerKeep innerTypes (nestedShell p.outer outerKeep) (List.ofFn ordinary ++ exitTypes)
  ordinaryRoutes : ∀ i, (p.outer.rows (outerKeep i.succ)).checkRoutes?
    (layout p.inner.payload (List.ofFn ordinary ++ exitTypes)) [ordinary i] = some (p.commonOrdinary i)
  anchors : ∀ i, i ∈ p.anchors q

end Silmaril.Isotope.LambdaSSA.NestedAdmission.Finite.Mixed
