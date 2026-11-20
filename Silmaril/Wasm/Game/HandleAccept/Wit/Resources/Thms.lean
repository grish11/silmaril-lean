module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Resources.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Resources

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime

private theorem takeWith_map {E : CoreEngine} {World α β : Type}
    (cx : LiftLowerContext E) (resource : RtId) (slot : Nat)
    (result : HandleObjId → Nat → α) (map : α → β) :
    (takeWith cx resource slot result : P E World α).bind (fun value => Prog.pure (map value)) =
      takeWith cx resource slot (fun identity rep => map (result identity rep)) := by
  simp only [takeWith, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.pure_bind']

/-- Erasing the owning identity gives exactly the legacy reference lift, including
the removal-first failure behavior. -/
theorem take_representation {E : CoreEngine} {World : Type} (limits : Component.Limits)
    (cx : LiftLowerContext E) (resource : RtId) (slot : Nat) :
    (take (World := World) limits cx resource slot).bind
      (fun owner => Prog.pure (Owned.representation (resource := resource) owner)) =
      liftOwn limits cx resource slot :=
  takeWith_map cx resource slot Owned.mk Owned.representation

end Silmaril.Wasm.Game.HandleAccept.Wit.Resources
