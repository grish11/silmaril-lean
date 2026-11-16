module

public import Silmaril.Logic.Prolog.Source.Syntax.Defs
public import Silmaril.Logic.Prolog.Definite.Thms

@[expose] public section
namespace Silmaril.Logic.Prolog.Source
open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Examples

/-- Only occurring function/predicate profiles need interpretations. In
particular a constant-free vocabulary can still admit an empty carrier. -/
structure Vocabulary where
  functions : List (FunctionName × Nat)
  predicates : List (String × Nat)
  deriving DecidableEq

abbrev FunctionSymbol (V : Vocabulary) (n : Nat) :=
  {name : FunctionName // (name, n) ∈ V.functions}
abbrev PredicateSymbol (V : Vocabulary) (n : Nat) :=
  {name : String // (name, n) ∈ V.predicates}

def Vocabulary.signature (V : Vocabulary) : FOL.Signature where
  S := Unit
  Op n _ _ := FunctionSymbol V n
  Rel n _ := PredicateSymbol V n

/-- A finite scoped source term, independently interpreted before translation
into the public first-order term language. -/
inductive Term (V : Vocabulary) (scope : Nat) where
  | var : Fin scope → Term V scope
  | app {n : Nat} (symbol : FunctionSymbol V n)
      (arguments : Fin n → Term V scope) : Term V scope

namespace Term
variable {V : Vocabulary} {scope : Nat}

def encode : Term V scope → EQ.Term V.signature.toSignature (fun _ : Fin scope => ()) ()
  | .var i => .var i
  | .app f args => .app f (fun i => (args i).encode)

def eval (M : FOL.Structure V.signature) (ρ : Fin scope → M.carrier ()) :
    Term V scope → M.carrier ()
  | .var i => ρ i
  | .app f args => M.op (w := fun _ => ()) (s := ()) f (fun i => (args i).eval M ρ)

theorem eval_encode (M : FOL.Structure V.signature) (ρ : Fin scope → M.carrier ())
    (t : Term V scope) : t.encode.eval M.toAlgebra ρ = t.eval M ρ := by
  induction t with
  | var i => rfl
  | app f args ih =>
    change M.op f (fun i => (args i).encode.eval M.toAlgebra ρ) =
      M.op f (fun i => (args i).eval M ρ)
    exact congrArg (M.op f) (funext ih)

end Term

structure Atom (V : Vocabulary) (scope : Nat) where
  arity : Nat
  predicate : PredicateSymbol V arity
  arguments : Fin arity → Term V scope

namespace Atom
variable {V : Vocabulary} {scope : Nat}

def encode (a : Atom V scope) : Definite.Atom V.signature (fun _ : Fin scope => ()) :=
  ⟨a.arity, fun _ => (), a.predicate, fun i => (a.arguments i).encode⟩

def Holds (M : FOL.Structure V.signature) (ρ : Fin scope → M.carrier ())
    (a : Atom V scope) : Prop := M.rel a.predicate (fun i => (a.arguments i).eval M ρ)

theorem encode_holds (M : FOL.Structure V.signature) (ρ : Fin scope → M.carrier ())
    (a : Atom V scope) : a.encode.Holds M ρ ↔ a.Holds M ρ := by
  simp only [encode, Definite.Atom.Holds, Holds, Term.eval_encode]

end Atom

structure Clause (V : Vocabulary) where
  context : List Variable
  head : Atom V context.length
  body : List (Atom V context.length)

structure Query (V : Vocabulary) where
  context : List Variable
  goals : List (Atom V context.length)

inductive Sentence (V : Vocabulary) where
  | clause : Clause V → Sentence V
  | query : Query V → Sentence V

namespace Clause
variable {V : Vocabulary}

def encode (c : Clause V) : Definite.Clause V.signature :=
  ⟨c.context.length, fun _ => (), c.body.map Atom.encode, c.head.encode⟩

def Holds (M : FOL.Structure V.signature) (c : Clause V) : Prop :=
  ∀ ρ : Fin c.context.length → M.carrier (),
    (∀ a ∈ c.body, a.Holds M ρ) → c.head.Holds M ρ

theorem encode_holds (M : FOL.Structure V.signature) (c : Clause V) :
    c.encode.Holds M ↔ c.Holds M := by
  constructor
  · intro h ρ hb
    apply (c.head.encode_holds M ρ).mp
    apply h ρ
    intro b hb'
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb'
    exact (a.encode_holds M ρ).mpr (hb a ha)
  · intro h ρ hb
    apply (c.head.encode_holds M ρ).mpr
    apply h ρ
    intro a ha
    exact (a.encode_holds M ρ).mp (hb a.encode (List.mem_map.mpr ⟨a, ha, rfl⟩))

end Clause

namespace Query
variable {V : Vocabulary}

def encode (q : Query V) : Definite.Query V.signature :=
  ⟨q.context.length, fun _ => (), q.goals.map Atom.encode⟩

def Holds (M : FOL.Structure V.signature) (q : Query V) : Prop :=
  ∃ ρ : Fin q.context.length → M.carrier (), ∀ a ∈ q.goals, a.Holds M ρ

theorem encode_holds (M : FOL.Structure V.signature) (q : Query V) :
    q.encode.Holds M ↔ q.Holds M := by
  constructor
  · rintro ⟨ρ, h⟩
    exact ⟨ρ, fun a ha => (a.encode_holds M ρ).mp
      (h a.encode (List.mem_map.mpr ⟨a, ha, rfl⟩))⟩
  · rintro ⟨ρ, h⟩
    refine ⟨ρ, ?_⟩
    intro b hb
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
    exact (a.encode_holds M ρ).mpr (h a ha)

end Query

namespace Sentence
variable {V : Vocabulary}

def encode : Sentence V → Definite.Sentence V.signature
  | .clause c => .clause c.encode
  | .query q => .query q.encode

def Holds (M : FOL.Structure V.signature) : Sentence V → Prop
  | .clause c => c.Holds M
  | .query q => q.Holds M

theorem encode_holds (M : FOL.Structure V.signature) (s : Sentence V) :
    s.encode.Holds M ↔ s.Holds M := by
  cases s with
  | clause c => exact c.encode_holds M
  | query q => exact q.encode_holds M

end Sentence

def nativeRoom (V : Vocabulary) : Room.{0,0,1} :=
  ⟨Sentence V, Cat.of (FOL.Structure V.signature), fun M s => s.Holds M⟩

/-- The source interpreter and public declarative Prolog semantics agree on
every model, retaining all ordinary public structure homomorphisms. -/
def toDefinite (V : Vocabulary) : nativeRoom V ⟶ Definite.room V.signature :=
  ⟨Sentence.encode, 𝟭 _, Sentence.encode_holds⟩

theorem toDefinite_modelExpansive (V : Vocabulary) : (toDefinite V).ModelExpansive :=
  fun M => ⟨M, rfl⟩

end Silmaril.Logic.Prolog.Source
