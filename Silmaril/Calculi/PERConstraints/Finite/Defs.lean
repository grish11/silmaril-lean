module

public import Silmaril.Calculi.PERConstraints.Defs
public import Mathlib.Data.Multiset.MapFold

/-! Finite presentations of Boolean constraint formulae. Multiplicity matters
inside occurrence DISTINCT only, never at an AND or OR node. -/

@[expose] public section
namespace Silmaril.Calculi.PERConstraints

open Silmaril.Formats

variable {α Item Container : Type}

/-- Forget order and multiplicity, retaining just membership. -/
def members [Membership Item Container] (items : Container) : Set Item := {item | item ∈ items}

def EQList (model : PER α) (terms : List α) : Prop := EQ model (members terms)
def EQMultiset (model : PER α) (terms : Multiset α) : Prop := EQ model (members terms)

/-- Distinctness of multiset occurrences; `Pairwise` may use any list representative
because non-relatedness in a PER is symmetric. -/
def DISTINCTMultiset (model : PER α) (terms : Multiset α) : Prop :=
  (∀ term ∈ terms, model.Dom term) ∧ terms.Pairwise (fun left right => ¬model.rel left right)

/-- Embed multiset DISTINCT without dropping repeated occurrences. -/
noncomputable def Bound.ofMultisetDistinct (terms : Multiset α) : Bound α := .distinct terms.toList

def AllList (holds : Item → Prop) (items : List Item) : Prop := All holds (members items)
def AnyList (holds : Item → Prop) (items : List Item) : Prop := Any holds (members items)
def AllMultiset (holds : Item → Prop) (items : Multiset Item) : Prop := All holds (members items)
def AnyMultiset (holds : Item → Prop) (items : Multiset Item) : Prop := Any holds (members items)

/-- Conjunction encoded as singleton clauses. -/
def CNF.ofAnd (atoms : Set (Bound α)) : CNF α := (fun atom => ({atom} : Set (Bound α))) '' atoms

/-- Disjunction encoded as one clause. -/
def CNF.ofOr (atoms : Set (Bound α)) : CNF α := {atoms}

def listRows (rows : List (List Item)) : Set (Set Item) := (fun row : List Item => members row) '' members rows
def multisetRows (rows : Multiset (Multiset Item)) : Set (Set Item) :=
  (fun row : Multiset Item => members row) '' members rows

def CNF.ofLists (clauses : List (List (Bound α))) : CNF α := listRows clauses
def DNF.ofLists (terms : List (List (Bound α))) : DNF α := listRows terms
def CNF.ofMultisets (clauses : Multiset (Multiset (Bound α))) : CNF α := multisetRows clauses
def DNF.ofMultisets (terms : Multiset (Multiset (Bound α))) : DNF α := multisetRows terms

/-- Infinitary dual of `CNF.toDNF`: take every clause meeting every DNF term. -/
def DNF.toCNF (sentence : DNF α) : CNF α :=
  {clause | ∀ term ∈ sentence, ∃ bound ∈ term, bound ∈ clause}

/-- Cartesian selection of one occurrence per row. Empty input returns the
single empty choice; any empty row gives no choices. No equality or model
evaluation is needed, and no duplicate choices are removed. -/
def choices : List (List Item) → List (List Item)
  | [] => [[]]
  | row :: rest =>
    let tailChoices := choices rest
    row.flatMap fun item => tailChoices.map (item :: ·)

/-- Finite DNF to the existing CNF sentence type, by distribution. -/
def DNF.finiteToCNF (terms : List (List (Bound α))) : CNF α := CNF.ofLists (choices terms)

/-- Finite CNF to DNF, by the same distribution with AND and OR swapped. -/
def CNF.finiteToDNF (clauses : List (List (Bound α))) : DNF α := DNF.ofLists (choices clauses)

end Silmaril.Calculi.PERConstraints
