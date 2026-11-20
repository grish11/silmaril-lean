module

public import Silmaril.Wasm.Component.Reference.Validation.Check.Defs

@[expose] public section

namespace Silmaril.Wasm.Component.IntrinsicWiring

open Silmaril.Wasm.Component.Validation Silmaril.Wasm.Component.Types

/-- Flat, payload-independent commands. Nested component binders and resource
declarations are not modeled by this fragment. Commands retain the reference
validator's exact scoping, subtyping and canonical ABI checks. -/
inductive Command where
  | instance_ (expr : Syntax.CoreInstanceExpr)
  | alias (expr : Syntax.Alias)
  | funcType (type : Syntax.FuncType)
  | canon (expr : Syntax.Canon)
  | export_ (name : Syntax.ExternName) (item : Syntax.SortIdx Syntax.Sort_)

def Command.toDef {M : Type} : Command → Syntax.Definition M
  | .instance_ expr => .coreInstance expr
  | .alias expr => .alias expr
  | .funcType type => .type (.func type)
  | .canon expr => .canon expr
  | .export_ name item => .export_ name item none

def Command.check {X : Type} (feat : Features) (profile : DefProfile X) (state : DefState X)
    (cmd : Command) : Except ValidationError (DefState X) :=
  checkDef? feat profile (fun _ : Unit => none) [] state cmd.toDef

/-- Each constructor advances the real reference component declaration scope.
The `core` constructor fixes the named Core interface supplied by the payload. -/
inductive Step {X M : Type} (feat : Features) (profile : DefProfile X)
    (interface? : M → Option (CoreModuleType X)) : DefState X → DefState X → Type where
  | core {state : DefState X} (payload : M) (interface : CoreModuleType X)
      (checked : interface? payload = some interface) :
      Step feat profile interface? state (state.step (state.st.withCtx (state.ctx.pushCoreModule interface).2))
  | command {before after : DefState X} (cmd : Command) (checked : cmd.check feat profile before = .ok after) :
      Step feat profile interface? before after

variable {X M N : Type} {feat : Features} {profile : DefProfile X}
  {interfaces : M → Option (CoreModuleType X)} {targets : N → Option (CoreModuleType X)}
  {before middle after : DefState X}

def Step.erase : Step feat profile interfaces before after → Syntax.Definition M
  | .core payload _ _ => .coreModule payload
  | .command cmd _ => cmd.toDef

def Step.map (f : M → N) (preserve : ∀ {payload type}, interfaces payload = some type → targets (f payload) = some type) :
    Step feat profile interfaces before after → Step feat profile targets before after
  | .core payload type checked => .core (f payload) type (preserve checked)
  | .command cmd checked => .command cmd checked

inductive Program {X M : Type} (feat : Features) (profile : DefProfile X)
    (interface? : M → Option (CoreModuleType X)) : DefState X → DefState X → Type where
  | nil {state : DefState X} : Program feat profile interface? state state
  | cons {before middle after : DefState X} : Step feat profile interface? before middle →
      Program feat profile interface? middle after → Program feat profile interface? before after

def Program.erase : {before after : DefState X} → Program feat profile interfaces before after → Syntax.Component M
  | _, _, .nil => []
  | _, _, .cons step tail => step.erase :: tail.erase

/-- Composition of declaration fragments needs the same intermediate scope,
including resolved module and instance interfaces. It is not arbitrary linking
of two independently closed binaries. -/
def Program.then : {before middle after : DefState X} →
    Program feat profile interfaces before middle → Program feat profile interfaces middle after →
    Program feat profile interfaces before after
  | _, _, _, .nil, tail => tail
  | _, _, _, .cons head rest, tail => .cons head (rest.then tail)

def Program.map (f : M → N) (preserve : ∀ {payload type}, interfaces payload = some type → targets (f payload) = some type) :
    {before after : DefState X} → Program feat profile interfaces before after → Program feat profile targets before after
  | _, _, .nil => .nil
  | _, _, .cons step tail => .cons (step.map f preserve) (tail.map f preserve)

end Silmaril.Wasm.Component.IntrinsicWiring
