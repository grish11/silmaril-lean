module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Exits.Check.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Trim.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.LabelRenaming.Restriction.Check.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution.KnownTag.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Defs

/-! # Admission for a nested Unit-payload CFG with two ordered exits -/

@[expose] public section

universe v

namespace Silmaril.Isotope.LambdaSSA.NestedAdmission

open Semantics.Categorical (retainLabelIndex)

variable {Φ : Type v} [HasTy Φ (Ty Empty)]

abbrev unitTy : Ty Empty := .unit
abbrev pairTy : Ty Empty := .product .unit .unit
abbrev exits : LCtx (Ty Empty) := [unitTy, pairTy]

/-- The inner CFG has two slots, with slot zero retained. -/
def keep : Fin 1 ↪ Fin 2 := ⟨fun _ => 0, by intro a b _; exact Subsingleton.elim a b⟩

abbrev labelIndex := retainLabelIndex keep

/-- The local repeat may be tagged. The outer repeat is tagged, and the two
actual exits carry Unit and Unit × Unit unchanged. -/
def layout (taggedInner : Bool) : RouteLayout Empty :=
  [(unitTy, if taggedInner then some .inl else none), (unitTy, some .inl), (unitTy, none), (pairTy, none)]

/-- Read the known arm after replacing the newest slot by the chosen injection.
The original sum may occur in the written arm. -/
def selectTag? (tag : CaseTag) : Region Φ → Option (Region Φ)
  | .case (.var 0) l r =>
      some (((tag.select l r).substVars (Tm.liftSubst (Tm.replaceNewest (tag.inject (.var 0))))).substVars
        (Tm.singleSubst (.var 0)))
  | _ => none

def selectLeft? (r : Region Φ) : Option (Region Φ) := selectTag? .inl r

def innerTag? : Region Φ → Option Bool
  | .br 0 (.var 0) => some false
  | .br 0 (.inl (.var 0)) => some true
  | _ => none

def innerEntry (taggedInner : Bool) : Region Φ :=
  .br 0 (if taggedInner then .inl (.var 0) else .var 0)

structure Plan (Φ : Type v) where
  outer : Region Φ
  entry : Region Φ
  rows : Fin 2 → Region Φ
  taggedInner : Bool
  selected : Region Φ
  common : Region Φ

/-- Admit a singleton outer CFG that initializes a known left tag and
dispatches through a case on its block parameter. The selected arm must be
a two-slot CFG. Its entry selects slot zero. Every written inner transfer
must avoid slot one. The selected live row must pass the constructor
route checker at the combined inner and enclosing label interface. -/
def check? : Region Φ → Option (Plan Φ)
  | .cfg (.br 0 (.inl .unit)) 1 blocks =>
      let outer := blocks 0
      (selectLeft? outer).bind fun chosen =>
      match chosen with
      | .cfg entry 2 rows =>
          (entry.restrictLabels? 4 labelIndex).bind fun entry' =>
          (Region.checkFamily 2 (fun i => (rows i).restrictLabels? 4 labelIndex)).bind fun rows' =>
          match innerTag? entry' with
          | none => none
          | some tag =>
              (if tag then selectLeft? (rows' 0) else some (rows' 0)).bind fun selected =>
              (selected.checkRoutes? (layout tag) [unitTy, unitTy]).bind fun common =>
                some ⟨outer, entry', rows', tag, selected, common⟩
      | _ => none
  | _ => none

/-- The result does not rule on unrecognized syntax. -/
inductive Comparison where
  | certified
  | unknown
  deriving DecidableEq, Repr

def compare? (r : Region Φ) : Comparison :=
  if (check? r).isSome then .certified else .unknown

/-- Evidence obtained by traversal, retaining the original outer syntax and
the original inner arity. The compact rows have only a labelling change. -/
structure Plan.Valid (r : Region Φ) (p : Plan Φ) : Prop where
  root : r = .cfg (.br 0 (.inl .unit)) 1 (fun _ => p.outer)
  outer : Region.PruneConstructorTests (p.outer.substVars (Tm.replaceNewest (.inl (.var 0))))
    (.cfg (p.entry.renameLabels labelIndex) 2 (fun i => (p.rows i).renameLabels labelIndex))
  entry : p.entry = innerEntry p.taggedInner
  entryScope : p.entry.LabelsBound 4
  rowScope : ∀ i, (p.rows i).LabelsBound 4
  row : if p.taggedInner then
    Region.PruneConstructorTests ((p.rows 0).substVars (Tm.replaceNewest (.inl (.var 0)))) p.selected
    else p.rows 0 = p.selected
  routes : CheckedRoutes (layout p.taggedInner) [unitTy, unitTy] p.common p.selected

end Silmaril.Isotope.LambdaSSA.NestedAdmission
