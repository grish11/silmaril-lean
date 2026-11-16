module

public import Silmaril.Logic.Egg.Source.Named.Resolution.Defs
public import Silmaril.Logic.Egglog.Source.Named.Parser.Defs

@[expose] public section
namespace Silmaril.Logic.Egg.Source.Named.Parser
open Silmaril.Logic.Smt

/-- Authored many-sorted grammar. The result annotation is mandatory. The
reader budget is derived from the complete S-expression, never a fixed cap. -/
def term : Nat → SE → Option RawTerm
  | 0, _ => none
  | _ + 1, .list [.atom "var", .atom name] => some (.var name)
  | fuel + 1, .list (.atom "app" :: .atom name :: .atom result :: arguments) =>
      (arguments.mapM (term fuel)).map (RawTerm.ofArgs name result)
  | _, _ => none

def term? (e : SE) : Option RawTerm :=
  term (Silmaril.Logic.Egglog.Source.Named.Parser.nodes e + 1) e

def equality : SE → Option RawEquality
  | .list [.atom "equal", left, right] => do
      pure ⟨← term? left, ← term? right⟩
  | _ => none

def rule : SE → Option RawRule
  | .list [.atom "rewrite", .atom name, .list context, .list guards, conclusion] => do
      pure ⟨name, ← context.mapM Silmaril.Logic.Egglog.Source.Named.Parser.binding,
        ← guards.mapM equality, ← equality conclusion⟩
  | _ => none

/-- Every parsed form must be a complete rule, including the final form. -/
def readProgram (bytes : List UInt8) : Option RawProgram := do
  let forms ← readForms bytes
  forms.mapM rule

def compileSupplied (D : Declarations) (bytes : List UInt8) :
    Option (List (Core.Rule D.signature)) := do
  resolveProgram? D (← readProgram bytes)

def compileInferred (bytes : List UInt8) :
    Option (Σ D : Declarations, List (Core.Rule D.signature)) := do
  inferProgram? (← readProgram bytes)

def encodeTerm : RawTerm → SE
  | .var name => .list [.atom "var", .atom name]
  | .app name result n arguments => .list (.atom "app" :: .atom name :: .atom result ::
      List.ofFn (fun i : Fin n => encodeTerm (arguments i)))

def encodeEquality (e : RawEquality) : SE :=
  .list [.atom "equal", encodeTerm e.left, encodeTerm e.right]

def encodeRule (r : RawRule) : SE :=
  .list [.atom "rewrite", .atom r.name,
    .list (r.context.map (fun b => .list [.atom b.name, .atom b.sort])),
    .list (r.guards.map encodeEquality), encodeEquality r.conclusion]

end Silmaril.Logic.Egg.Source.Named.Parser
