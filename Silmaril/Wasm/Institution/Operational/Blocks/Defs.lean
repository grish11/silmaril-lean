module

public import Silmaril.Wasm.Institution.Operational.Locals.Thms

/-!
# Single scalar blocks

An isolated block has no inputs and has zero or one numeric result. Its body
is flat local code. The positive rules cover block entry, reduction under its
administrative label, and normal exit.
-/

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.Blocks

open Silmaril.Logic.Operational Silmaril.Logic.Operational.SOS Silmaril.Semantics.SOS
open Silmaril.Wasm.Execution.Runtime (Value)

inductive State where
  | block (result : Option NumType) (body : Locals.State)
  | label (result : Option NumType) (body : Locals.State)
  | done (locals result : List Value)

inductive Judgment where
  | body (edge : Locals.Judgment)
  | block (source target : State)

inductive RuleInstance : Rule Judgment → Prop where
  | body {r : Rule Locals.Judgment} (rule : Locals.RuleInstance r) :
      RuleInstance ⟨r.premises.map .body, .body r.conclusion⟩
  | enter (result : Option NumType) (a : Locals.State) :
      RuleInstance ⟨[], .block (.block result a) (.label result a)⟩
  | reduce (result : Option NumType) (a b : Locals.State) :
      RuleInstance ⟨[.body (a, b)], .block (.label result a) (.label result b)⟩
  | exit (result : Option NumType) (ls vs : List Value) :
      RuleInstance ⟨[], .block (.label result ⟨ls, Locals.values vs⟩) (.done ls vs)⟩

def shape : SOS.Shape.{0} :=
  ⟨⟨State, Unit⟩, Judgment, fun (a, _, b) => .block a b⟩

def presentation : SOS.Presentation := ⟨shape, {r | RuleInstance r}⟩

abbrev Edge (a b : State) := presentation.Derives (.block a b)
abbrev Runs := Relation.ReflTransGen Edge

def Admitted (types : List NumType) (result : Option NumType) : State → Prop
  | .block declared a | .label declared a =>
      declared = result ∧ Locals.Admitted types result.toList a
  | .done ls vs => ls.map Value.type = types ∧ (vs.map Value.type).reverse = result.toList

end Silmaril.Wasm.Institution.Operational.Blocks
