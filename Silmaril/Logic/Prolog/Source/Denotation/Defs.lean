module

public import Silmaril.Logic.Prolog.Source.Compilation.Defs
public import Mathlib.Data.List.NodupEquivFin

@[expose] public section
namespace Silmaril.Logic.Prolog.Source
open Silmaril.Logic.Institution.Examples

/-- A named assignment exists only on the finite sentence context. An empty
context has an assignment even when the model carrier is empty. -/
abbrev NamedValuation {V : Vocabulary} (M : FOL.Structure V.signature)
    (names : List Variable) := {v : Variable // v ∈ names} → M.carrier ()

def NamedValuation.indexed {V : Vocabulary} {M : FOL.Structure V.signature}
    {names : List Variable} (ρ : NamedValuation M names) : Fin names.length → M.carrier () :=
  fun i => ρ ⟨names.get i, List.get_mem names i⟩

/-- Direct named-tree denotation: variables are looked up by their source name,
and applications use the stated finite vocabulary. No resolver, native term,
translation or global assignment occurs in this definition. -/
def NamedTerm.Denotes {V : Vocabulary} (M : FOL.Structure V.signature)
    {names : List Variable} (ρ : NamedValuation M names) : NamedTerm → M.carrier () → Prop
  | .var v, x => ∃ h : v ∈ names, ρ ⟨v, h⟩ = x
  | .app name n args, x => ∃ known : (name, n) ∈ V.functions,
      ∃ values : Fin n → M.carrier (),
        (∀ i, (args i).Denotes M ρ (values i)) ∧
          M.op (w := fun _ => ()) (s := ()) ⟨name, known⟩ values = x

def NamedAtom.Holds {V : Vocabulary} (M : FOL.Structure V.signature)
    {names : List Variable} (ρ : NamedValuation M names) (a : NamedAtom) : Prop :=
  ∃ known : (a.predicate, a.arity) ∈ V.predicates,
    ∃ values : Fin a.arity → M.carrier (),
      (∀ i, (a.arguments i).Denotes M ρ (values i)) ∧ M.rel ⟨a.predicate, known⟩ values

/-- Named clauses and queries bind their finite context universally and
existentially, respectively. Keeping the context explicit also describes erased
native sentences whose supplied contexts may contain unused names. -/
def NamedSentence.HoldsIn {V : Vocabulary} (M : FOL.Structure V.signature)
    (names : List Variable) : NamedSentence → Prop
  | .clause head body => ∀ ρ : NamedValuation M names,
      (∀ a ∈ body, a.Holds M ρ) → head.Holds M ρ
  | .query goals => ∃ ρ : NamedValuation M names, ∀ a ∈ goals, a.Holds M ρ

def NamedSentence.Holds {V : Vocabulary} (M : FOL.Structure V.signature)
    (s : NamedSentence) : Prop := s.HoldsIn M s.variables

def NamedSentence.isClause : NamedSentence → Bool
  | .clause _ _ => true
  | .query _ => false

/-- Select clause or query meaning without asserting the other kind. -/
def NamedSentence.HoldsPart {V : Vocabulary} (M : FOL.Structure V.signature)
    (clauses : Bool) (s : NamedSentence) : Prop :=
  if s.isClause = clauses then s.Holds M else True

def Sentence.HoldsPart {V : Vocabulary} (M : FOL.Structure V.signature)
    (clauses : Bool) (s : Sentence V) : Prop :=
  if s.erase.isClause = clauses then s.Holds M else True

end Silmaril.Logic.Prolog.Source
