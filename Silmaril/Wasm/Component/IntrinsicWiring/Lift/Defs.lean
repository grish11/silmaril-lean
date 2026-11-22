module

public import Silmaril.Wasm.Component.IntrinsicWiring.Defs

@[expose] public section

namespace Silmaril.Wasm.Component.IntrinsicWiring

open Silmaril.Wasm.Component.Validation Silmaril.Wasm.Component.Types

variable {X M N : Type} {feat : Features} {profile : DefProfile X}
  {interfaces : M → Option (CoreModuleType X)} {targets : N → Option (CoreModuleType X)}

/-- A closed declaration program indexed by its checked reference interface. -/
structure Closed (feat : Features) (profile : DefProfile X) (interfaces : M → Option (CoreModuleType X))
    (interface : ComponentType Nat X) where
  state : DefState X
  program : Program feat profile interfaces initState state
  done : ComponentDone state.ctx
  interface_eq : componentTypeOfDefs state.ctx = interface

def Closed.map {interface : ComponentType Nat X} (f : M → N)
    (preserve : ∀ {payload type}, interfaces payload = some type → targets (f payload) = some type)
    (component : Closed feat profile interfaces interface) : Closed feat profile targets interface :=
  ⟨component.state, component.program.map f preserve, component.done, component.interface_eq⟩

def Closed.erase {interface : ComponentType Nat X}
    (component : Closed feat profile interfaces interface) : Syntax.Component M := component.program.erase

/-- A position in the checked export table, at its actual name and entity type. -/
structure Exposure (interface : ComponentType Nat X) (name : String) (entity : Entity Nat X) where
  index : Fin interface.exports.length
  entry : interface.exports[index] = (name, entity)

/-- Recognize the command part of the flat grammar; do not drop export ascriptions. -/
def Command.read {M : Type} : (raw : Syntax.Definition M) → Option {cmd : Command // cmd.toDef = raw}
  | .coreInstance expr => some ⟨.instance_ expr, rfl⟩
  | .alias expr => some ⟨.alias expr, rfl⟩
  | .type (.func type) => some ⟨.funcType type, rfl⟩
  | .canon expr => some ⟨.canon expr, rfl⟩
  | .export_ name item none => some ⟨.export_ name item, rfl⟩
  | _ => none

/-- Reconstruct a step, using the existing checker for the actual scope transition. -/
def Step.lift? (feat : Features) (profile : DefProfile X) (interfaces : M → Option (CoreModuleType X))
    (before : DefState X) (raw : Syntax.Definition M) :
    Option (Σ after, {step : Step feat profile interfaces before after // step.erase = raw}) :=
  match raw with
  | .coreModule payload =>
    match checked : interfaces payload with
    | some type => some ⟨_, .core payload type checked, rfl⟩
    | none => none
  | raw => do
    let ⟨cmd, exactDef⟩ ← Command.read raw
    match checked : cmd.check feat profile before with
    | .ok after => some ⟨after, .command cmd checked, exactDef⟩
    | .error _ => none

/-- Successful lifting reconstructs the original definitions, not a normalized component. -/
def Program.lift? (feat : Features) (profile : DefProfile X) (interfaces : M → Option (CoreModuleType X)) :
    (before : DefState X) → (raw : Syntax.Component M) →
    Option (Σ after, {program : Program feat profile interfaces before after // program.erase = raw})
  | before, [] => some ⟨before, .nil, rfl⟩
  | before, head :: tail => do
    let ⟨middle, step, headEq⟩ ← Step.lift? feat profile interfaces before head
    let ⟨after, rest, tailEq⟩ ← Program.lift? feat profile interfaces middle tail
    pure ⟨after, .cons step rest, congrArg₂ List.cons headEq tailEq⟩

def Closed.lift? (feat : Features) (profile : DefProfile X) (interfaces : M → Option (CoreModuleType X))
    (raw : Syntax.Component M) : Option (Σ interface, {component : Closed feat profile interfaces interface //
      component.erase = raw}) := do
  let ⟨state, program, exactDefs⟩ ← Program.lift? feat profile interfaces initState raw
  if done : ComponentDone state.ctx then
    some ⟨componentTypeOfDefs state.ctx, ⟨state, program, done, rfl⟩, exactDefs⟩
  else none

end Silmaril.Wasm.Component.IntrinsicWiring
