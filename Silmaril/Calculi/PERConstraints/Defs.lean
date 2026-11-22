module

public import Silmaril.Calculi.PERConstraints.Syntax.Defs
public import Silmaril.Logic.Institution.Basic
public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Set.Pairwise.Basic

/-! Constraints on the support and equivalence classes of a PER. The institution
uses set EQ and occurrence DISTINCT; distinctness of a set of values is a
separate operation, since arbitrary reindexing may identify its elements. -/

@[expose] public section
namespace Silmaril.Calculi.PERConstraints

open CategoryTheory Silmaril.Formats Silmaril.Logic.Institution

variable {α β : Type}

/-- All designated terms are related, including the diagonal. The empty set
is vacuous and a singleton tests validity. A nonempty set lies in one class. -/
def EQ (model : PER α) (terms : Set α) : Prop :=
  ∀ left ∈ terms, ∀ right ∈ terms, model.rel left right

def EQFinset (model : PER α) (terms : Finset α) : Prop := EQ model (terms : Set α)

/-- All designated terms must be valid, and different elements must occupy
different classes. Empty is vacuous; a singleton still tests validity. -/
def DISTINCT (model : PER α) (terms : Set α) : Prop :=
  (∀ term ∈ terms, model.Dom term) ∧ terms.Pairwise (fun left right => ¬model.rel left right)

def DISTINCTFinset (model : PER α) (terms : Finset α) : Prop := DISTINCT model (terms : Set α)

/-- Distinctness of occurrences, not of the underlying set. In particular,
repeating any term makes the constraint unsatisfiable. -/
def DISTINCTList (model : PER α) (terms : List α) : Prop :=
  (∀ term ∈ terms, model.Dom term) ∧ terms.Pairwise (fun left right => ¬model.rel left right)

/-- The sum of the two atomic constraints that transport along arbitrary
syntax functions. Set DISTINCT is intentionally not a constructor. -/
inductive Bound (α : Type) where
  | eq (terms : Set α)
  | distinct (occurrences : List α)

def Bound.map (rename : α → β) : Bound α → Bound β
  | .eq terms => .eq (rename '' terms)
  | .distinct terms => .distinct (terms.map rename)

def Bound.Holds (model : PER α) : Bound α → Prop
  | .eq terms => EQ model terms
  | .distinct terms => DISTINCTList model terms

def Bound.ofFinsetEq (terms : Finset α) : Bound α := .eq (terms : Set α)

/-- Enumerate the source set before translation, so later renamings cannot erase
collisions. Choice of enumeration does not affect satisfaction. -/
noncomputable def Bound.ofFinsetDistinct (terms : Finset α) : Bound α := .distinct terms.toList

def All {Item : Type} (holds : Item → Prop) (items : Set Item) : Prop :=
  ∀ item ∈ items, holds item

def Any {Item : Type} (holds : Item → Prop) (items : Set Item) : Prop :=
  ∃ item ∈ items, holds item

def AllFinset {Item : Type} (holds : Item → Prop) (items : Finset Item) : Prop :=
  All holds (items : Set Item)

def AnyFinset {Item : Type} (holds : Item → Prop) (items : Finset Item) : Prop :=
  Any holds (items : Set Item)

/-- Conjunction of disjunctions. Empty conjunctions are true; empty clauses
are false. -/
abbrev CNF (α : Type) := Set (Set (Bound α))

/-- Disjunction of conjunctions. Empty disjunctions are false; empty terms
are true. -/
abbrev DNF (α : Type) := Set (Set (Bound α))

def CNF.Holds (model : PER α) (sentence : CNF α) : Prop := All (Any (Bound.Holds model)) sentence
def DNF.Holds (model : PER α) (sentence : DNF α) : Prop := Any (All (Bound.Holds model)) sentence

def CNF.map (rename : α → β) (sentence : CNF α) : CNF β :=
  (fun clause => Bound.map rename '' clause) '' sentence

def DNF.map (rename : α → β) (sentence : DNF α) : DNF β :=
  (fun term => Bound.map rename '' term) '' sentence

def CNF.ofFinsets (clauses : Finset (Finset (Bound α))) : CNF α :=
  (fun clause : Finset (Bound α) => (clause : Set (Bound α))) '' (clauses : Set _)

def DNF.ofFinsets (terms : Finset (Finset (Bound α))) : DNF α :=
  (fun term : Finset (Bound α) => (term : Set (Bound α))) '' (terms : Set _)

/-- The disjunction of sets of atoms meeting every clause. This is an
infinitary semantic translation, not a finite enumeration procedure. -/
def CNF.toDNF (sentence : CNF α) : DNF α :=
  {term | ∀ clause ∈ sentence, ∃ bound ∈ clause, bound ∈ term}

def CNF.SAT (sentence : CNF α) : Prop := ∃ model : PER α, sentence.Holds model
def CNF.UNSAT (sentence : CNF α) : Prop := ∀ model : PER α, ¬sentence.Holds model

def DNF.SAT (sentence : DNF α) : Prop := ∃ model : PER α, sentence.Holds model
def DNF.UNSAT (sentence : DNF α) : Prop := ∀ model : PER α, ¬sentence.Holds model

/-- A dictionary is a partial association from keys to atomic constraints.
Key names and duplicate values do not affect conjunctive satisfaction. -/
abbrev Dictionary (Key α : Type) := Key → Option (Bound α)

def Dictionary.Holds {Key : Type} (model : PER α) (dict : Dictionary Key α) : Prop :=
  ∀ key bound, dict key = some bound → bound.Holds model

def Dictionary.toCNF {Key : Type} (dict : Dictionary Key α) : CNF α :=
  {clause | ∃ key bound, dict key = some bound ∧ clause = {bound}}

def Dictionary.SAT {Key : Type} (dict : Dictionary Key α) : Prop :=
  ∃ model : PER α, dict.Holds model

def Dictionary.UNSAT {Key : Type} (dict : Dictionary Key α) : Prop :=
  ∀ model : PER α, ¬dict.Holds model

abbrev Model (signature : Syntax) := PER signature.Term

def reduct {source target : Syntax} (rename : source ⟶ target) (model : Model target) : Model source :=
  model.pull rename.term

/-- Institution model arrows are discrete. PER-preserving maps in the total
category are separate: such maps need not reflect relation or domain. -/
def room (signature : Syntax) : Room.{0,0,0} :=
  ⟨CNF signature.Term, Cat.of (Discrete (Model signature)), fun model sentence => CNF.Holds model.as sentence⟩

def modelReduct {source target : Syntax} (rename : source ⟶ target) :
    (room target).Mod ⥤ (room source).Mod :=
  Discrete.functor fun model => Discrete.mk (reduct rename model)

end Silmaril.Calculi.PERConstraints
