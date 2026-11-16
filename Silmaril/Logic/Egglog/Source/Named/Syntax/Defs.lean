module

public import Silmaril.Prelude.Defs

@[expose] public section
namespace Silmaril.Logic.Egglog.Source.Named

/-- Explicit tags distinguish variables from nullary constructors. Partial table
calls are atoms, never total terms. Argument order and arbitrary arity are retained. -/
inductive RawTerm where
  | var (name : String)
  | app (name : String) (arity : Nat) (arguments : Fin arity → RawTerm)

def RawTerm.ofArgs (name : String) (arguments : List RawTerm) : RawTerm :=
  .app name arguments.length arguments.get

inductive RawAtom where
  | equal (left right : RawTerm)
  | relation (name : String) (arity : Nat) (arguments : Fin arity → RawTerm)
  | row (name : String) (arity : Nat) (arguments : Fin arity → RawTerm) (value : RawTerm)

structure Binding where
  name : String
  sort : String
  deriving DecidableEq, Repr

/-- Whole ordered contexts include unused variables, even at empty sorts. -/
abbrev Context := List Binding

inductive RawSentence where
  | rule (context : Context) (body : List RawAtom) (head : RawAtom)
  | query (context : Context) (goals : List RawAtom)

structure TotalDeclaration where
  name : String
  inputs : List String
  output : String
  deriving DecidableEq, Repr

structure RelationDeclaration where
  name : String
  inputs : List String
  deriving DecidableEq, Repr

inductive RawDeclaration where
  | sort (name : String)
  | constructor (declaration : TotalDeclaration)
  | relation (declaration : RelationDeclaration)
  | function (declaration : TotalDeclaration)
  deriving DecidableEq, Repr

/-- A whole program compiles to a theory, not one arbitrarily selected sentence. -/
structure RawProgram where
  declarations : List RawDeclaration
  sentences : List RawSentence

end Silmaril.Logic.Egglog.Source.Named
