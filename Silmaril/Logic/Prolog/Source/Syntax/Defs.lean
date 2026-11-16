module

public import Silmaril.Prelude.Defs

@[expose] public section
namespace Silmaril.Logic.Prolog.Source

/-- Named variables share a binding within one sentence. Every occurrence of
`_` receives its own anonymous identifier from the source parser. -/
inductive Variable where
  | named : String → Variable
  | anonymous : Nat → Variable
  deriving DecidableEq, Repr

/-- Integer tokens and atoms remain distinct: `1` is not the atom `'1'`.
Here integers are constructor symbols; arithmetic builtins are a separate layer. -/
inductive FunctionName where
  | atom : String → FunctionName
  | integer : Int → FunctionName
  deriving DecidableEq, Repr

inductive NamedTerm where
  | var : Variable → NamedTerm
  | app (name : FunctionName) (arity : Nat) (arguments : Fin arity → NamedTerm) : NamedTerm

/-- Parser-facing constructor for an ordinary finite argument list. -/
def NamedTerm.ofArgs (name : FunctionName) (arguments : List NamedTerm) : NamedTerm :=
  .app name arguments.length arguments.get

structure NamedAtom where
  predicate : String
  arity : Nat
  arguments : Fin arity → NamedTerm

def NamedAtom.ofArgs (name : String) (arguments : List NamedTerm) : NamedAtom :=
  ⟨name, arguments.length, arguments.get⟩

inductive NamedSentence where
  | clause (head : NamedAtom) (body : List NamedAtom) : NamedSentence
  | query (goals : List NamedAtom) : NamedSentence

end Silmaril.Logic.Prolog.Source
