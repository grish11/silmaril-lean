module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Admission.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Trim.Check.Defs

/-! # Admission with a finite retained inner interface -/

@[expose] public section

universe v

namespace Silmaril.Isotope.LambdaSSA.NestedAdmission.Finite

open Semantics.Categorical (retainLabelIndex CfgRestriction)

variable {Φ : Type v} [HasTy Φ (Ty Empty)]

/-- Prepend the ordinary local targets of a finite inner table. -/
def innerLayout {m : Nat} (types : Fin m → Ty Empty) (out : RouteLayout Empty) : RouteLayout Empty :=
  List.ofFn (fun i => (types i, none)) ++ out

/-- The outer repeat uses a left tag. Each actual exit keeps its position. -/
def enclosingLayout (payload : Ty Empty) (exitTypes : LCtx (Ty Empty)) : RouteLayout Empty :=
  (payload, some .inl) :: exitTypes.map (fun A => (A, none))

def layout {m : Nat} (types : Fin m → Ty Empty) (exitTypes : LCtx (Ty Empty) := exits)
    (payload : Ty Empty := unitTy) : RouteLayout Empty :=
  List.ofFn (fun i => (types i, none)) ++ (payload, some .inl) :: exitTypes.map (fun A => (A, none))

/-- Branch targets in the transfer and case fragment checked by `checkRoutes?`. -/
def branchesTo (target : Nat) : Region Φ → Bool
  | .br i _ => i == target
  | .case _ l r => branchesTo target l || branchesTo target r
  | _ => false

/-- Saturate written type anchors for a bounded number of transfer steps. -/
def anchorWorklist {m : Nat} (seed : Fin m → Bool) (edge : Fin m → Fin m → Bool) :
    Nat → List (Fin m)
  | 0 => (List.finRange m).filter seed
  | d + 1 =>
      let known := anchorWorklist seed edge d
      (List.finRange m).filter fun i => seed i || known.any fun j => edge j i

/-- Retained slots with a written synthesizing path from the entry, counting
the number of row edges after the entry edge. This tracks typing constraints;
it does not assert that all written cases are taken at runtime. -/
def anchored {m : Nat} (entry : Region Φ) (rows : Fin m → Region Φ) : Nat → List (Fin m) :=
  anchorWorklist (fun i => branchesTo i entry) (fun j i => branchesTo i (rows j))

/-- An inner restriction and its checked common entry and retained rows. -/
structure InnerPlan (Φ : Type v) (m n : Nat) where
  table : CfgRestriction Φ n
  commonEntry : Region Φ
  commonRows : Fin m → Region Φ

def InnerPlan.common {m n : Nat} (p : InnerPlan Φ m n) : Region Φ :=
  .cfg p.commonEntry m p.commonRows

/-- Check a finite inner mask against an arbitrary ordered outward route
layout. Anchor all retained local types in the captured payload context. -/
def checkInner? {k n : Nat} (keep : Fin (k + 1) ↪ Fin (n + 1)) (types : Fin (k + 1) → Ty Empty)
    (payload : Ty Empty) (out : RouteLayout Empty) (body : Region Φ) : Option (InnerPlan Φ (k + 1) (n + 1)) :=
  (CfgRestriction.check? keep out.length body).bind fun table =>
  (table.entry.checkRoutes? (innerLayout types out) [payload]).bind fun entry =>
  (Region.checkFamily (k + 1) (fun i =>
    (table.rows (keep i)).checkRoutes? (innerLayout types out) [types i, payload])).bind fun rows =>
  if (List.finRange (k + 1)).all (fun i => (anchored entry rows k).contains i) then
    some ⟨table, entry, rows⟩
  else none

structure InnerPlan.Valid {k n : Nat} (p : InnerPlan Φ (k + 1) (n + 1))
    (keep : Fin (k + 1) ↪ Fin (n + 1)) (types : Fin (k + 1) → Ty Empty)
    (payload : Ty Empty) (out : RouteLayout Empty) (body : Region Φ) : Prop where
  table : p.table.Valid keep out.length body
  entryRoute : p.table.entry.checkRoutes? (innerLayout types out) [payload] = some p.commonEntry
  rowRoutes : ∀ i, (p.table.rows (keep i)).checkRoutes? (innerLayout types out) [types i, payload] =
    some (p.commonRows i)
  paths : ∀ i, i ∈ anchored p.commonEntry p.commonRows k

structure Plan (Φ : Type v) (m n : Nat) where
  initializer : Tm Φ
  payload : Ty Empty
  outer : Region Φ
  entry : Region Φ
  rows : Fin n → Region Φ
  commonEntry : Region Φ
  commonRows : Fin m → Region Φ

/-- The common inner table read from the accepted entry and rows. -/
def Plan.commonInner {m n : Nat} (p : Plan Φ m n) : Region Φ :=
  .cfg p.commonEntry m p.commonRows

/-- Restore the original selected table's inner label indices. -/
def Plan.selectedInner {m n : Nat} (p : Plan Φ m n) (keep : Fin m ↪ Fin n) : Region Φ :=
  .cfg (p.entry.renameLabels (retainLabelIndex keep)) n
    (fun i => (p.rows i).renameLabels (retainLabelIndex keep))

/-- Check a supplied retained interface and candidate payload types against
the written CFG. Synthesize the type of the outer left initializer and
check all written inner label targets. The entry and retained rows must
synthesize the admitted payloads, and each retained input must have a path
to anchor its type. -/
def check? {k n : Nat} (keep : Fin (k + 1) ↪ Fin (n + 1)) (types : Fin (k + 1) → Ty Empty)
    (r : Region Φ) (exitTypes : LCtx (Ty Empty) := exits) : Option (Plan Φ (k + 1) (n + 1)) :=
  match r with
  | .cfg (.br 0 (.inl initializer)) 1 blocks =>
      let outer := blocks 0
      (initializer.synthRouteType? []).bind fun payload =>
      (selectLeft? outer).bind fun body =>
      (checkInner? keep types payload (enclosingLayout payload exitTypes) body).map fun p =>
        ⟨initializer, payload, outer, p.table.entry, p.table.rows, p.commonEntry, p.commonRows⟩
  | _ => none

def compare? {k n : Nat} (keep : Fin (k + 1) ↪ Fin (n + 1)) (types : Fin (k + 1) → Ty Empty)
    (r : Region Φ) (exitTypes : LCtx (Ty Empty) := exits) : Comparison :=
  if (check? keep types r exitTypes).isSome then .certified else .unknown

/-- The selected syntax, exact reindexing, route checks and written paths
recorded by successful admission. -/
structure Plan.Valid {k n : Nat} (keep : Fin (k + 1) ↪ Fin (n + 1)) (types : Fin (k + 1) → Ty Empty)
    (r : Region Φ) (p : Plan Φ (k + 1) (n + 1)) (exitTypes : LCtx (Ty Empty) := exits) : Prop where
  root : r = .cfg (.br 0 (.inl p.initializer)) 1 (fun _ => p.outer)
  initializerType : p.initializer.synthRouteType? [] = some p.payload
  outer : Region.PruneConstructorTests (p.outer.substVars (Tm.replaceNewest (.inl (.var 0))))
    (.cfg (p.entry.renameLabels (retainLabelIndex keep)) (n + 1)
      (fun i => (p.rows i).renameLabels (retainLabelIndex keep)))
  entryScope : p.entry.LabelsBound (k + 1 + (exitTypes.length + 1))
  rowScope : ∀ i, (p.rows i).LabelsBound (k + 1 + (exitTypes.length + 1))
  entryRoute : p.entry.checkRoutes? (layout types exitTypes p.payload) [p.payload] = some p.commonEntry
  rowRoutes : ∀ i, (p.rows (keep i)).checkRoutes? (layout types exitTypes p.payload) [types i, p.payload] =
    some (p.commonRows i)
  paths : ∀ i, i ∈ anchored p.commonEntry p.commonRows k

end Silmaril.Isotope.LambdaSSA.NestedAdmission.Finite
