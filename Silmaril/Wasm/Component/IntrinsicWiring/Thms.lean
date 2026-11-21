module

public import Silmaril.Wasm.Component.IntrinsicWiring.Defs
public import Silmaril.Wasm.Component.Reference.Validation.Check.Thms
import Silmaril.Proofs.Wasm.Component.IntrinsicWiring

public section

namespace Silmaril.Wasm.Component.IntrinsicWiring

open Silmaril.Wasm.Component.Validation Silmaril.Wasm.Component.Types

variable {X M N : Type} {feat : Features} {profile : DefProfile X}
  {interfaces : M → Option (CoreModuleType X)} {targets : N → Option (CoreModuleType X)}
  {before middle after : DefState X}

@[simp] theorem Program.erase_nil : (Program.nil : Program feat profile interfaces before before).erase = [] := rfl

theorem Program.erase_then (left : Program feat profile interfaces before middle)
    (right : Program feat profile interfaces middle after) : (left.then right).erase = left.erase ++ right.erase :=
  Proofs.Wasm.Component.IntrinsicWiring.eraseThen left right

theorem Program.erase_map (f : M → N)
    (preserve : ∀ {payload type}, interfaces payload = some type → targets (f payload) = some type)
    (program : Program feat profile interfaces before after) :
    (program.map f preserve).erase = Syntax.Component.map f program.erase :=
  Proofs.Wasm.Component.IntrinsicWiring.eraseMap f preserve program

theorem Program.map_then (f : M → N)
    (preserve : ∀ {payload type}, interfaces payload = some type → targets (f payload) = some type)
    (left : Program feat profile interfaces before middle) (right : Program feat profile interfaces middle after) :
    (left.then right).map f preserve = (left.map f preserve).then (right.map f preserve) :=
  Proofs.Wasm.Component.IntrinsicWiring.mapThen f preserve left right

theorem Program.checked (program : Program feat profile interfaces before after) :
    checkDefs? feat profile interfaces [] before program.erase = .ok after :=
  Proofs.Wasm.Component.IntrinsicWiring.checkProgram program

theorem Program.check_closed (program : Program feat profile interfaces initState after)
    (done : ComponentDone after.ctx) : check? feat profile interfaces program.erase = .ok (componentTypeOfDefs after.ctx) := by
  simp [check?, Program.checked program, done]

theorem Program.sound (program : Program feat profile interfaces initState after) (done : ComponentDone after.ctx) :
    ValidComponent feat profile interfaces program.erase (componentTypeOfDefs after.ctx) :=
  check?_sound (program.check_closed done)

end Silmaril.Wasm.Component.IntrinsicWiring
