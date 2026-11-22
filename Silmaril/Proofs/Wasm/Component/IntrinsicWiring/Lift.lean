module

public import Silmaril.Wasm.Component.IntrinsicWiring.Lift.Defs

public section

namespace Silmaril.Proofs.Wasm.Component.IntrinsicWiring.Lift

open Silmaril.Wasm.Component Silmaril.Wasm.Component.IntrinsicWiring
open Silmaril.Wasm.Component.Validation Silmaril.Wasm.Component.Types

variable {X M : Type} {feat : Features} {profile : DefProfile X}
  {interfaces : M → Option (CoreModuleType X)} {before after : DefState X}

theorem step (typed : Step feat profile interfaces before after) :
    Step.lift? feat profile interfaces before typed.erase = some ⟨after, typed, rfl⟩ := by
  cases typed with
  | core payload type checked =>
    simp only [Step.erase, Step.lift?]
    split <;> rename_i result
    · have eq := Option.some.inj (result.symm.trans checked)
      cases eq
      rfl
    · simp_all
  | command cmd checked =>
    cases cmd <;> simp only [Step.erase, Command.toDef, Step.lift?, Command.read, bind, Option.bind] <;>
      split <;> rename_i result <;> first
      | have eq := Except.ok.inj (result.symm.trans checked)
        cases eq
        rfl
      | simp_all

theorem program (typed : Program feat profile interfaces before after) :
    Program.lift? feat profile interfaces before typed.erase = some ⟨after, typed, rfl⟩ := by
  induction typed with
  | nil => rfl
  | cons head tail ih => simp [Program.erase, Program.lift?, step head, ih]

end Silmaril.Proofs.Wasm.Component.IntrinsicWiring.Lift
