module

public import Silmaril.Logic.Egglog.Source.Named.Declarations.Thms
public import Silmaril.Logic.Egg.Core.Defs

@[expose] public section
namespace Silmaril.Logic.Egg.Source.Named

/-- Every application carries its result sort. This annotation enables actual
profile inference without assuming a single sort or a supplied vocabulary. -/
inductive RawTerm where
  | var (name : String)
  | app (name result : String) (arity : Nat) (arguments : Fin arity → RawTerm)

def RawTerm.ofArgs (name result : String) (arguments : List RawTerm) : RawTerm :=
  .app name result arguments.length arguments.get

structure RawEquality where
  left : RawTerm
  right : RawTerm

/-- Labels are provenance; direction does not change conditional equation truth.
The context includes unused and right-only variables, in original order. -/
structure RawRule where
  name : String
  context : Silmaril.Logic.Egglog.Source.Named.Context
  guards : List RawEquality
  conclusion : RawEquality

abbrev RawProgram := List RawRule

/-- The reused vocabulary is explicitly restricted to total constructors. -/
structure Declarations where
  checked : Silmaril.Logic.Egglog.Source.Named.Declarations
  noRelations : checked.data.relations = []
  noFunctions : checked.data.functions = []

abbrev Declarations.signature (D : Declarations) : Core.Signature :=
  D.checked.signature.toSignature

abbrev CheckedContext (D : Declarations) := Silmaril.Logic.Egglog.Source.Named.CheckedContext D.checked

end Silmaril.Logic.Egg.Source.Named
