module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Admission.Finite.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Trim.Check.Defs

/-! # Written outer tables with finitely many selected nested rows -/

@[expose] public section

universe v

namespace Silmaril.Isotope.LambdaSSA.NestedAdmission.Finite.MultiNested

open Semantics.Categorical (CfgRestriction)

variable {Φ : Type v} [HasTy Φ (Ty Empty)] {m n : Nat}

/-- The selected arm for each nested row. Ordinary rows have no tag. -/
def selection (nested : Fin m → Bool) (tags : Fin m → CaseTag) (i : Fin m) : Option CaseTag :=
  if nested i then some (tags i) else none

/-- Selected slots require their chosen injection. Ordered exits use their
written payloads directly. -/
def layout (P : Fin m → Ty Empty) (nested : Fin m → Bool) (L : LCtx (Ty Empty))
    (tags : Fin m → CaseTag := fun _ => .inl) : RouteLayout Empty :=
  List.ofFn (fun i => (P i, selection nested tags i)) ++ L.map (fun A => (A, none))

/-- Check injection heads throughout written code, even in rows or arms
that the typed comparison will discard. Inner local labels precede
the enclosing interface. -/
def checkTransferTags (tags : List (Option CaseTag)) : Region Φ → Bool
  | .br i a => (a.routePayload? tags[i]?.join).isSome
  | .case _ l r => checkTransferTags tags l && checkTransferTags tags r
  | .let₁ _ body | .let₂ _ body => checkTransferTags tags body
  | .cfg entry size rows =>
      let inner := List.replicate size none ++ tags
      checkTransferTags inner entry && (List.finRange size).all (fun i => checkTransferTags inner (rows i))

/-- Check the entry and all original rows on the scope-checked compact
outer interface. Reindexing changes label numbers only. -/
def checkTableTags (out : RouteLayout Empty) (table : CfgRestriction Φ n) : Bool :=
  let tags := out.map Prod.snd
  checkTransferTags tags table.entry && (List.finRange n).all (fun i => checkTransferTags tags (table.rows i))

/-- Candidate retained labels and payloads for one selected inner table.
Different selected rows may supply different arities and masks. -/
structure InnerMask where
  retainedTail : Nat
  writtenTail : Nat
  keep : Fin (retainedTail + 1) ↪ Fin (writtenTail + 1)
  types : Fin (retainedTail + 1) → Ty Empty

def InnerMask.singleton (A : Ty Empty) : InnerMask :=
  ⟨0, 0, Function.Embedding.refl _, fun _ => A⟩

inductive RowPlan (Φ : Type v) where
  | ordinary (common : Region Φ)
  | nested (mask : InnerMask) (plan : InnerPlan Φ (mask.retainedTail + 1) (mask.writtenTail + 1))

def RowPlan.commonRegion : RowPlan Φ → Region Φ
  | .ordinary row => row
  | .nested _ plan => plan.common

def RowPlan.targets (i : Nat) : RowPlan Φ → Bool
  | .ordinary row => branchesTo i row
  | .nested mask plan =>
      let target := mask.retainedTail + 1 + i
      branchesTo target plan.commonEntry ||
        (List.finRange (mask.retainedTail + 1)).any fun j => branchesTo target (plan.commonRows j)

/-- Ordinary rows are branch/case rows. Check a selected arm's finite inner
mask in the already-bound payload context. Omitting a mask uses the
singleton inner interface. -/
def checkRow? (choice : Option CaseTag) (A : Ty Empty) (out : RouteLayout Empty) (r : Region Φ)
    (mask : Option InnerMask := none) : Option (RowPlan Φ) :=
  match choice with
  | none => (r.checkRoutes? out [A]).map RowPlan.ordinary
  | some tag =>
      let mask := mask.getD (InnerMask.singleton A)
      (selectTag? tag r).bind fun selected =>
      (checkInner? mask.keep mask.types A out selected).map (RowPlan.nested mask)

inductive RowPlan.Valid (A : Ty Empty) (out : RouteLayout Empty) (r : Region Φ) : Option CaseTag → RowPlan Φ → Prop
  | ordinary {common} (route : r.checkRoutes? out [A] = some common) :
      Valid A out r none (.ordinary common)
  | nested {mask plan body tag} (prune : Region.PruneConstructorTests
      (r.substVars (Tm.replaceNewest (tag.inject (.var 0)))) body)
      (typed : InnerPlan.Valid plan mask.keep mask.types A out body) :
      Valid A out r (some tag) (.nested mask plan)

structure Plan (Φ : Type v) (m n : Nat) where
  outer : CfgRestriction Φ n
  entry : Region Φ
  rows : Fin m → RowPlan Φ

def Plan.anchors (p : Plan Φ m n) (depth : Nat) : List (Fin m) :=
  anchorWorklist (fun i => branchesTo i p.entry) (fun j i => (p.rows j).targets i) depth

/-- Check the literal full table and all retained rows at the candidate
payloads. Each selected row uses its own tag, with left as the default.
A bounded worklist must reach every retained slot by checked transfers,
including transfers out of a selected inner block. -/
def check? (keep : Fin m ↪ Fin n) (P : Fin m → Ty Empty) (forms : Fin m → Bool)
    (r : Region Φ) (L : LCtx (Ty Empty) := exits)
    (innerMasks : Fin m → Option InnerMask := fun _ => none)
    (tags : Fin m → CaseTag := fun _ => .inl) : Option (Plan Φ m n) :=
  let out := layout P forms L tags
  (CfgRestriction.check? keep L.length r).bind fun c =>
  if checkTableTags out c then
    (c.entry.checkRoutes? out []).bind fun entry =>
    (Region.checkFamily m (fun i =>
      checkRow? (selection forms tags i) (P i) out (c.rows (keep i)) (innerMasks i))).bind fun rows =>
    let p := Plan.mk c entry rows
    if (List.finRange m).all (fun i => (p.anchors m).contains i) then some p else none
  else none

def compare? (keep : Fin m ↪ Fin n) (P : Fin m → Ty Empty) (forms : Fin m → Bool)
    (r : Region Φ) (L : LCtx (Ty Empty) := exits)
    (innerMasks : Fin m → Option InnerMask := fun _ => none)
    (tags : Fin m → CaseTag := fun _ => .inl) : Comparison :=
  if (check? keep P forms r L innerMasks tags).isSome then .certified else .unknown

structure Plan.Valid (p : Plan Φ m n) (keep : Fin m ↪ Fin n) (P : Fin m → Ty Empty) (forms : Fin m → Bool)
    (r : Region Φ) (L : LCtx (Ty Empty)) (tags : Fin m → CaseTag := fun _ => .inl) : Prop where
  outer : p.outer.Valid keep L.length r
  writtenTags : checkTableTags (layout P forms L tags) p.outer = true
  entry : p.outer.entry.checkRoutes? (layout P forms L tags) [] = some p.entry
  rows : ∀ i, (p.rows i).Valid (P i) (layout P forms L tags) (p.outer.rows (keep i)) (selection forms tags i)
  anchors : ∀ i, i ∈ p.anchors m

end Silmaril.Isotope.LambdaSSA.NestedAdmission.Finite.MultiNested
