module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Modules.Defs
public import Silmaril.Logic.Kore.GeneralFixedPoint.BooleanTheory.Syntax
public import Silmaril.Logic.Kore.GeneralFixedPoint.Predicates.Thms

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Logic.Kore.GeneralFixedPoint.BooleanTheory
open Predicates
open CategoryTheory Silmaril.Logic.Institution

namespace Source

def sorts (s : Source) : List String := s.declarations.filterMap fun d =>
  match d.declaration with | .sort n => some n | _ => none

def symbols (s : Source) : List (Kore.Modules.NamedSymbol × Attributes) :=
  s.declarations.zipIdx.filterMap fun (d, i) =>
    match d.declaration with
    | .symbol p => some (⟨⟨s.moduleName, i⟩, p.profile⟩, p.attributes)
    | _ => none

def scope (s : Source) : Kore.Modules.Scope :=
  ⟨s.declarations.zipIdx.filterMap (fun (d, i) => match d.declaration with
    | .sort n => some (⟨s.moduleName, i⟩, n) | _ => none), s.symbols.map Prod.fst, []⟩

/-- One homogeneous value sort; constructor declarations in this profile are
functional constants. No no-confusion/coverage law is silently added. -/
def valid (s : Source) : Bool :=
  match s.sorts with
  | [sort] =>
    let names := sort :: (s.symbols.map (fun d => d.1.declaration.name))
    names.Nodup && names.all (fun n => n.toList.head?.any Operational.Text.letter) &&
      s.symbols.all (fun (d, a) =>
        d.declaration.arguments.all (· == sort) && d.declaration.result == sort &&
        (!a.constructor || (a.functional && d.declaration.arguments.isEmpty)))
  | _ => false
end Source

/-- Free names are derived from the original raw operands, not conventional
Boolean variable spellings. Bound names are removed before outer quantification. -/
def RawPredicate.names (fuel : Nat) : RawPredicate → Names
  | .top | .bottom => []
  | .equal _ p q | .member _ p q =>
      (Checking.freeNames false fuel [] p ++ Checking.freeNames false fuel [] q).eraseDups
  | .neg p => p.names fuel
  | .conj p q | .disj p q => (p.names fuel ++ q.names fuel).eraseDups
  | .ex name _ p => (p.names fuel).filter (fun n => n.1 != name)

def checkPredicate (scope : Kore.Modules.Scope) (objects : Names)
    (fuel : Nat) : RawPredicate → Option (Predicate scope objects)
  | .top => some .top
  | .bottom => some .bottom
  | .equal sort p q => do
      let p ← checkValue scope objects sort fuel p
      let q ← checkValue scope objects sort fuel q
      return .equal sort p q
  | .member sort p q => do
      let p ← checkValue scope objects sort fuel p
      let q ← checkValue scope objects sort fuel q
      return .member sort p q
  | .neg p => return .neg (← checkPredicate scope objects fuel p)
  | .conj p q => do
      let p ← checkPredicate scope objects fuel p
      let q ← checkPredicate scope objects fuel q
      return .conj p q
  | .disj p q => do
      let p ← checkPredicate scope objects fuel p
      let q ← checkPredicate scope objects fuel q
      return .disj p q
  | .ex name bound p =>
      if Kore.Modules.Checking.namedSort scope bound then
        return .ex name bound (← checkPredicate scope ((name, bound)::objects) fuel p)
      else none

inductive Sentence (scope : Kore.Modules.Scope) where
  | value (objects : Names) (sort : String) (p : Value scope objects sort)
  | scheme (parameter : String) (objects : Names) (p : Predicate scope objects)

def checkSentence (source : Source) (fuel : Nat) : RawSentence → Option (Sentence source.scope)
  | .value raw => do
      let sort ← Checking.resultSort source.scope raw
      let objects := (Checking.freeNames false fuel [] raw).eraseDups
      return .value objects sort (← checkValue source.scope objects sort fuel raw)
  | .scheme parameter raw =>
      if source.sorts.contains parameter then none else do
        let objects := raw.names fuel
        return .scheme parameter objects (← checkPredicate source.scope objects fuel raw)

structure LocatedSentence (scope : Kore.Modules.Scope) where
  origin : Kore.Modules.Origin
  location : Kore.Modules.Location
  raw : RawSentence
  checked : Sentence scope

/-- Checked sentences retain their own raw source and original declaration index. -/
def checkSentences (source : Source) (fuel : Nat) (claims : Bool) :
    Option (List (LocatedSentence source.scope)) :=
  source.declarations.zipIdx.filterMapM fun (d, i) => do
    let raw := match d.declaration, claims with
      | .axiomDecl p, false | .claim p, true => some p
      | _, _ => none
    match raw with
    | none => return none
    | some p => return some ⟨⟨source.moduleName, i⟩, d.location, p, ← checkSentence source fuel p⟩

structure Package where
  text : String
  source : Source
  parsed : Syntax.parse text = some source
  fuel : Nat
  valid : source.valid = true
  axioms : List (LocatedSentence source.scope)
  checked_axioms : checkSentences source fuel false = some axioms
  claims : List (LocatedSentence source.scope)
  checked_claims : checkSentences source fuel true = some claims

def checkText (fuel : Nat) (text : String) : Option Package := do
  match parsed : Syntax.parse text with
  | none => none
  | some source =>
    if valid : source.valid = true then
      match ha : checkSentences source fuel false with
      | none => none
      | some axioms =>
        match hc : checkSentences source fuel true with
        | none => none
        | some claims => some ⟨text, source, parsed, fuel, valid, axioms, ha, claims, hc⟩
    else none

/-- A functional attribute is a total singleton graph on every actual tuple.
Constructor metadata identifies designated functional constants; disjointness
and coverage are obligations of source axioms, not extra assumed equations. -/
structure Functional (source : Source)
    (M : Matching.GeneralFixedPoint.Model source.scope.signature) : Prop where
  graph : ∀ d ∈ source.symbols, d.2.functional = true →
    ∀ {n inputs output} (op : source.scope.signature.operations n inputs output),
    op.val = d.1 → ∀ args, ∃ x, M.operation op args = {x}

structure Model (p : Package) where
  base : Matching.GeneralFixedPoint.Model p.source.scope.signature
  functional : Functional p.source base

instance (p : Package) : Category (Model p) where
  Hom M N := M.base ⟶ N.base
  id M := 𝟙 M.base
  comp f g := f ≫ g
  id_comp f := Category.id_comp f
  comp_id f := Category.comp_id f
  assoc f g h := Category.assoc f g h

def Sentence.Satisfies {scope} (q : Sentence scope)
    (M : Matching.GeneralFixedPoint.Model scope.signature) : Prop :=
  match q with
  | .value _ _ p => ∀ v x, x ∈ p.denote M v
  | .scheme _ _ p => p.Satisfies M

/-- The translation of a scheme is its whole infinite family of native result
sort instances, rather than silently replacing its parameter by Bool. -/
def Sentence.lower {scope} : Sentence scope →
    Set (Matching.GeneralFixedPoint.Sentence (Predicates.signature scope))
  | .value objects sort p => {⟨0, objects.length, context [], context objects, sort, p.lower,
      by rw [Value.lower, Matching.GeneralFixedPoint.Pattern.admissible_map]; exact p.admitted⟩}
  | .scheme _ objects p => {q | ∃ result, q = ⟨0, objects.length, context [], context objects,
      result, p.lower result, p.lower_admitted result⟩}

end Silmaril.Logic.Kore.GeneralFixedPoint.BooleanTheory
