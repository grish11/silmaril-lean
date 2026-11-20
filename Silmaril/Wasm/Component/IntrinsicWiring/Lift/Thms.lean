module

public import Silmaril.Wasm.Component.IntrinsicWiring.Lift.Defs
public import Silmaril.Wasm.Component.IntrinsicWiring.Thms
import Silmaril.Proofs.Wasm.Component.IntrinsicWiring.Lift

public section

namespace Silmaril.Wasm.Component.IntrinsicWiring

open Silmaril.Wasm.Component.Validation Silmaril.Wasm.Component.Types

variable {X M N : Type} {feat : Features} {profile : DefProfile X}
  {interfaces : M → Option (CoreModuleType X)} {targets : N → Option (CoreModuleType X)}
  {interface : ComponentType Nat X}

theorem Closed.checked (component : Closed feat profile interfaces interface) :
    check? feat profile interfaces component.erase = .ok interface :=
  (component.program.check_closed component.done).trans (congrArg Except.ok component.interface_eq)

theorem Closed.sound (component : Closed feat profile interfaces interface) :
    ValidComponent feat profile interfaces component.erase interface :=
  check?_sound component.checked

theorem Closed.erase_map (component : Closed feat profile interfaces interface) (f : M → N)
    (preserve : ∀ {payload type}, interfaces payload = some type → targets (f payload) = some type) :
    (component.map f preserve).erase = Syntax.Component.map f component.erase :=
  component.program.erase_map f preserve

theorem Program.lift_erase {before after : DefState X} (typed : Program feat profile interfaces before after) :
    Program.lift? feat profile interfaces before typed.erase = some ⟨after, typed, rfl⟩ :=
  Proofs.Wasm.Component.IntrinsicWiring.Lift.program typed

theorem Closed.lift_erase (typed : Closed feat profile interfaces interface) :
    Closed.lift? feat profile interfaces typed.erase = some ⟨interface, typed, rfl⟩ := by
  obtain ⟨state, program, done, rfl⟩ := typed
  simp [Closed.lift?, Closed.erase, program.lift_erase, done]

theorem Closed.lift_isSome_iff (raw : Syntax.Component M) :
    (Closed.lift? feat profile interfaces raw).isSome ↔
      ∃ (interface : ComponentType Nat X) (typed : Closed feat profile interfaces interface), typed.erase = raw := by
  constructor
  · intro found
    obtain ⟨interface, typed, exactDefs⟩ := (Closed.lift? feat profile interfaces raw).get found
    exact ⟨interface, typed, exactDefs⟩
  · rintro ⟨interface, typed, rfl⟩
    simp [typed.lift_erase]

end Silmaril.Wasm.Component.IntrinsicWiring
