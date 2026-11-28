module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Defs
public import Silmaril.Languages.Python.Core.Text.Slice.Defs

/-! # Checked operands for live text slice guards -/

@[expose] public section
namespace Silmaril.Languages.Python.Compile.ModuleEntry.Functions.TextSlice

open Source (Expr Name Scope)

inductive Atom where
  | literal (value : Core.Text)
  | global (name : Name)

structure Operand where
  atom : Atom
  bounds : Option Core.SliceBounds

def bound? : Option Expr → Option (Option Int)
  | none | some .none_ => some none
  | some expression => (integerLiteral? expression).map some

def bounds? (start stop step : Option Expr) : Option Core.SliceBounds := do
  return ⟨← bound? start, ← bound? stop, ← bound? step⟩

inductive AtomTranslation (scope : Scope) : Expr → Atom → Prop where
  | literal {points value} (checked : Core.Text.ofPoints? points = some value) :
      AtomTranslation scope (.text points) (.literal value)
  | global (name : Name) (reference : GlobalReference scope name) :
      AtomTranslation scope (.name name) (.global name)

def atom? (scope : Scope) : (source : Expr) → Option {atom // AtomTranslation scope source atom}
  | .name name =>
    (globalReference? scope name).map fun reference => ⟨.global name, .global name reference⟩
  | .text points =>
    match checked : Core.Text.ofPoints? points with
    | some value => some ⟨.literal value, .literal checked⟩
    | none => none
  | _ => none

inductive OperandTranslation (scope : Scope) : Expr → Operand → Prop where
  | plain {source atom} (checked : AtomTranslation scope source atom) :
      OperandTranslation scope source ⟨atom, none⟩
  | slice {receiver start stop step atom bounds}
      (checked : AtomTranslation scope receiver atom) (bounded : bounds? start stop step = some bounds) :
      OperandTranslation scope (.slice receiver start stop step) ⟨atom, some bounds⟩

def operand? (scope : Scope) : (source : Expr) → Option {operand // OperandTranslation scope source operand}
  | .slice receiver start stop step => do
    let atom ← atom? scope receiver
    match bounded : bounds? start stop step with
    | some bounds => some ⟨⟨atom.val, some bounds⟩, .slice atom.property bounded⟩
    | none => none
  | source => (atom? scope source).map fun atom => ⟨⟨atom.val, none⟩, .plain atom.property⟩

structure Guard where
  left : Operand
  right : Operand
  exception : Name

inductive Failure where
  | missingName (name : Name)
  | outsideTextProfile
  | zeroStep
  | reachedRaise
  deriving DecidableEq, Repr

def Atom.eval {Value : Type} (lookup : Name → Option Value) (asText : Value → Option Core.Text) :
    Atom → Except Failure (Option Core.Text)
  | .literal value => .ok (some value)
  | .global name => do
    let some value := lookup name | throw (.missingName name)
    return asText value

def Operand.eval {Value : Type} (lookup : Name → Option Value) (asText : Value → Option Core.Text)
    (operand : Operand) : Except Failure (Option Core.Text) := do
  let value ← operand.atom.eval lookup asText
  match operand.bounds with
  | none => pure value
  | some slice =>
    let some text := value | throw .outsideTextProfile
    match text.slice? slice with
    | some result => pure (some result)
    | none => throw .zeroStep

/-- Equal text skips the entire raise arm. An unequal comparison reaches
its live exception-name lookup, with invocation outside this profile. -/
def Guard.eval {Value : Type} (lookup : Name → Option Value) (asText : Value → Option Core.Text)
    (guard : Guard) : Except Failure Unit := do
  let left ← guard.left.eval lookup asText
  let right ← guard.right.eval lookup asText
  let some left := left | throw .outsideTextProfile
  let some right := right | throw .outsideTextProfile
  if left.points = right.points then pure ()
  else if (lookup guard.exception).isNone then throw (.missingName guard.exception)
  else throw .reachedRaise

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions.TextSlice
