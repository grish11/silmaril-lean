module

public import Silmaril.Logic.Kore.GeneralFixedPoint.BooleanTheory.Defs
public import Silmaril.Logic.Reachability.Derivation.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.CheckedRewrites
open Predicates

/-- Original raw guarded rewrite operands. Sorts are concrete declared names;
free set variables and symbol/sort polymorphism are outside this profile. -/
structure RawRewrite where
  configurationSort : String
  lhs : RawPattern
  guard : BooleanTheory.RawPredicate
  rhs : RawPattern
  deriving Repr

/-- Original raw value interpretation, independent of all native lowerings. -/
def rawValue {scope : Kore.Modules.Scope}
    (M : Matching.GeneralFixedPoint.Model scope.signature) (fuel : Nat)
    (objects : Names) (v : Env M objects) (sort : String) (raw : RawPattern) :
    Set (M.carrier sort) :=
  (Semantics.denote scope M fuel []
    (Semantics.interpret M objects (fun i => {v i})) sort raw).getD ∅

/-- Direct recursion on the original guard. Equality compares complete sets;
membership means overlap. Quantifiers extend the original capture environment. -/
def rawPredicateTruth {scope : Kore.Modules.Scope}
    (M : Matching.GeneralFixedPoint.Model scope.signature) (fuel : Nat) :
    (objects : Names) → BooleanTheory.RawPredicate → Env M objects → Prop
  | _, .top, _ => True
  | _, .bottom, _ => False
  | objects, .equal sort p q, v => rawValue M fuel objects v sort p = rawValue M fuel objects v sort q
  | objects, .member sort p q, v =>
      (rawValue M fuel objects v sort p ∩ rawValue M fuel objects v sort q).Nonempty
  | objects, .neg p, v => ¬ rawPredicateTruth M fuel objects p v
  | objects, .conj p q, v => rawPredicateTruth M fuel objects p v ∧ rawPredicateTruth M fuel objects q v
  | objects, .disj p q, v => rawPredicateTruth M fuel objects p v ∨ rawPredicateTruth M fuel objects q v
  | objects, .ex name bound p, v =>
      ∃ x : M.carrier bound, rawPredicateTruth M fuel ((name, bound) :: objects) p (Fin.cases x v)

/-- All endpoints and guard leaves are checked against ONE sorted context. -/
structure CheckedRewrite (scope : Kore.Modules.Scope) (cfg : String) where
  raw : RawRewrite
  fuel : Nat
  objects : Names
  configurationSort : raw.configurationSort = cfg
  lhs : Value scope objects cfg
  rhs : Value scope objects cfg
  guard : Predicate scope objects
  lhs_checked : checkValue scope objects cfg fuel raw.lhs = some lhs
  rhs_checked : checkValue scope objects cfg fuel raw.rhs = some rhs
  guard_checked : BooleanTheory.checkPredicate scope objects fuel raw.guard = some guard

/-- Free captures are collected jointly, including guard-only and RHS captures. -/
def captures (fuel : Nat) (raw : RawRewrite) : Names :=
  (Checking.freeNames false fuel [] raw.lhs ++ BooleanTheory.RawPredicate.names fuel raw.guard ++
    Checking.freeNames false fuel [] raw.rhs).eraseDups

/-- Repeated occurrences of the same name must have one sort. -/
def coherent (objects : Names) : Bool := decide (objects.map Prod.fst).Nodup

/-- Smart construction rejects invalid syntax rather than assuming adequacy.
Bound set variables remain available through the existing local-polarity checker. -/
def checkRewrite (scope : Kore.Modules.Scope) (cfg : String) (fuel : Nat)
    (raw : RawRewrite) : Option (CheckedRewrite scope cfg) := do
  if !Kore.Modules.Checking.namedSort scope cfg then none else
  if sort : raw.configurationSort = cfg then
    let objects := captures fuel raw
    if !coherent objects then none else do
      match hl : checkValue scope objects cfg fuel raw.lhs,
          hr : checkValue scope objects cfg fuel raw.rhs,
          hg : BooleanTheory.checkPredicate scope objects fuel raw.guard with
      | some lhs, some rhs, some guard =>
          some ⟨raw, fuel, objects, sort, lhs, rhs, guard, hl, hr, hg⟩
      | _, _, _ => none
  else none

/-- Declaration identities are not reconstructed from selected rule order. -/
structure LocatedRewrite (scope : Kore.Modules.Scope) (cfg : String) where
  origin : Kore.Modules.Origin
  location : Kore.Modules.Location
  checked : CheckedRewrite scope cfg

/-- Core checked system. Source traversal must separately establish visibility
and that this list consists of visible installed axioms, rather than claims. -/
structure CheckedRewriteSystem (scope : Kore.Modules.Scope) (cfg : String) where
  rules : List (LocatedRewrite scope cfg)

/-- Both raw endpoints use the same independently selected rule assignment. -/
def RawStep {scope cfg} (sys : CheckedRewriteSystem scope cfg)
    (M : Matching.GeneralFixedPoint.Model scope.signature) (w v : M.carrier cfg) : Prop :=
  ∃ i : Fin sys.rules.length,
    ∃ a : Env M sys.rules[i].checked.objects,
      w ∈ rawValue M sys.rules[i].checked.fuel sys.rules[i].checked.objects a cfg
        sys.rules[i].checked.raw.lhs ∧
      rawPredicateTruth M sys.rules[i].checked.fuel sys.rules[i].checked.objects
        sys.rules[i].checked.raw.guard a ∧
      v ∈ rawValue M sys.rules[i].checked.fuel sys.rules[i].checked.objects a cfg
        sys.rules[i].checked.raw.rhs

/-- Native matching syntax, with the predicate interpreted at configuration sort. -/
def CheckedRewrite.lowerLhs {scope cfg} (r : CheckedRewrite scope cfg) :
    NativePattern scope r.objects cfg := .conj r.lhs.lower (r.guard.lower cfg)

/-- Schemes execute actual native lowerings in the definedness expansion.
No source raw interpreter is called by either endpoint. -/
def lowerSchemes {scope cfg} (sys : CheckedRewriteSystem scope cfg)
    (M : Matching.GeneralFixedPoint.Model scope.signature) (i : Fin sys.rules.length) :
    Reachability.RuleSystem.Scheme (M.carrier cfg) where
  Parameters := Env M sys.rules[i].checked.objects
  lhs a w := w ∈ sys.rules[i].checked.lowerLhs.denote (expand M) a (fun j => j.elim0)
  rhs a v := v ∈ sys.rules[i].checked.rhs.lower.denote (expand M) a (fun j => j.elim0)

/-- Genuine source total-RHS obligation; successful syntax alone does not imply it. -/
def RawWellDefined {scope cfg} (sys : CheckedRewriteSystem scope cfg)
    (M : Matching.GeneralFixedPoint.Model scope.signature) : Prop :=
  ∀ (i : Fin sys.rules.length) (a : Env M sys.rules[i].checked.objects) (w : M.carrier cfg),
    w ∈ rawValue M sys.rules[i].checked.fuel sys.rules[i].checked.objects a cfg
      sys.rules[i].checked.raw.lhs →
    rawPredicateTruth M sys.rules[i].checked.fuel sys.rules[i].checked.objects
      sys.rules[i].checked.raw.guard a →
    ∃ v, v ∈ rawValue M sys.rules[i].checked.fuel sys.rules[i].checked.objects a cfg
      sys.rules[i].checked.raw.rhs

end Silmaril.Logic.Kore.GeneralFixedPoint.CheckedRewrites
