module

public import Silmaril.Logic.Prolog.Source.Native.Defs

@[expose] public section
namespace Silmaril.Logic.Prolog.Source

def NamedTerm.variables : NamedTerm → List Variable
  | .var v => [v]
  | .app _ n args => (List.ofFn (fun i : Fin n => (args i).variables)).flatten

def NamedTerm.functions : NamedTerm → List (FunctionName × Nat)
  | .var _ => []
  | .app name n args => (name, n) :: (List.ofFn (fun i : Fin n => (args i).functions)).flatten

def NamedAtom.variables (a : NamedAtom) : List Variable :=
  (List.ofFn (fun i : Fin a.arity => (a.arguments i).variables)).flatten

def NamedAtom.functions (a : NamedAtom) : List (FunctionName × Nat) :=
  (List.ofFn (fun i : Fin a.arity => (a.arguments i).functions)).flatten

def NamedSentence.atoms : NamedSentence → List NamedAtom
  | .clause head body => head :: body
  | .query goals => goals

/-- Bind each named/anonymous variable once, in order of first occurrence.
Anonymous parser identifiers have already distinguished each `_` occurrence. -/
def NamedSentence.variables (s : NamedSentence) : List Variable :=
  (s.atoms.flatMap NamedAtom.variables).eraseDups

/-- Symbol names are paired with their actual source arity; `f/1` and `f/2`
are distinct, and function and predicate vocabularies remain separate. -/
def inferVocabulary (sentences : List NamedSentence) : Vocabulary where
  functions := (sentences.flatMap (fun s => s.atoms.flatMap NamedAtom.functions)).eraseDups
  predicates := (sentences.flatMap (fun s => s.atoms.map (fun a => (a.predicate, a.arity)))).eraseDups

def findVariable? (v : Variable) : (names : List Variable) → Option (Fin names.length)
  | [] => none
  | name :: rest => if v = name then some 0 else (findVariable? v rest).map Fin.succ

/-- Sequence a finite tuple without losing its arity or rebuilding an unrelated
argument list. -/
def sequence? {α : Type} : (n : Nat) → (Fin n → Option α) → Option (Fin n → α)
  | 0, _ => some Fin.elim0
  | n + 1, f => do
    let first ← f 0
    let rest ← sequence? n (fun i => f i.succ)
    pure (Fin.cases first rest)

def resolveTerm? (V : Vocabulary) (names : List Variable) :
    NamedTerm → Option (Term V names.length)
  | .var v => (findVariable? v names).map Term.var
  | .app name n arguments => do
    let symbol : FunctionSymbol V n ←
      if known : (name, n) ∈ V.functions then some ⟨name, known⟩ else none
    let arguments ← sequence? n (fun i => resolveTerm? V names (arguments i))
    pure (.app symbol arguments)

def resolveAtom? (V : Vocabulary) (names : List Variable) (a : NamedAtom) :
    Option (Atom V names.length) := do
  let predicate : PredicateSymbol V a.arity ←
    if known : (a.predicate, a.arity) ∈ V.predicates then some ⟨a.predicate, known⟩ else none
  let arguments ← sequence? a.arity (fun i => resolveTerm? V names (a.arguments i))
  pure ⟨a.arity, predicate, arguments⟩

def resolveSentence? (V : Vocabulary) (s : NamedSentence) : Option (Sentence V) := do
  let names := s.variables
  match s with
  | .clause head body =>
    let head ← resolveAtom? V names head
    let body ← body.mapM (resolveAtom? V names)
    pure (.clause ⟨names, head, body⟩)
  | .query goals =>
    let goals ← goals.mapM (resolveAtom? V names)
    pure (.query ⟨names, goals⟩)

structure ResolvedProgram where
  vocabulary : Vocabulary
  sentences : List (Sentence vocabulary)

/-- Infer one shared signature for the entire unit, then resolve every sentence
against it. A query's local variables do not bind variables in program clauses. -/
def resolveProgram? (sentences : List NamedSentence) : Option ResolvedProgram := do
  let V := inferVocabulary sentences
  let resolved ← sentences.mapM (resolveSentence? V)
  pure ⟨V, resolved⟩

/-- Recover source names and profiles from a scoped term. -/
def Term.erase {V : Vocabulary} (names : List Variable) : Term V names.length → NamedTerm
  | .var i => .var (names.get i)
  | .app f args => .app f.val _ (fun i => (args i).erase names)

def Atom.erase {V : Vocabulary} (names : List Variable) (a : Atom V names.length) :
    NamedAtom := ⟨a.predicate.val, a.arity, fun i => (a.arguments i).erase names⟩

def Sentence.context {V : Vocabulary} : Sentence V → List Variable
  | .clause c => c.context
  | .query q => q.context

/-- Erasure preserves the clause/query distinction and all source atoms. -/
def Sentence.erase {V : Vocabulary} : Sentence V → NamedSentence
  | .clause c => .clause (c.head.erase c.context) (c.body.map (Atom.erase c.context))
  | .query q => .query (q.goals.map (Atom.erase q.context))

end Silmaril.Logic.Prolog.Source
