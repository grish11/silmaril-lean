module

public import Silmaril.Wasm.Component.IntrinsicWiring.Defs

public section

namespace Silmaril.Proofs.Wasm.Component.IntrinsicWiring

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Validation Silmaril.Wasm.Component.IntrinsicWiring
open Silmaril.Wasm.Component.Types

variable {X M N : Type} {feat : Features} {profile : DefProfile X}
  {interfaces : M → Option (CoreModuleType X)} {targets : N → Option (CoreModuleType X)}
  {before middle after : DefState X}

theorem checkStep (step : Step feat profile interfaces before after) :
    checkDef? feat profile interfaces [] before step.erase = .ok after := by
  cases step with
  | core payload type checked => simp [Step.erase, checkDef?, checkCoreModule?, checked]
  | command cmd checked =>
    cases cmd <;> exact checked

theorem checkProgram (program : Program feat profile interfaces before after) :
    checkDefs? feat profile interfaces [] before program.erase = .ok after := by
  induction program with
  | nil => rfl
  | cons step _ ih => simpa only [Program.erase, checkDefs?, checkStep step] using ih

theorem eraseThen (left : Program feat profile interfaces before middle)
    (right : Program feat profile interfaces middle after) : (left.then right).erase = left.erase ++ right.erase := by
  induction left with
  | nil => rfl
  | cons head _ ih => simp [Program.then, Program.erase, ih]

theorem eraseMap (f : M → N) (preserve : ∀ {payload type}, interfaces payload = some type → targets (f payload) = some type)
    (program : Program feat profile interfaces before after) :
    (program.map f preserve).erase = Syntax.Component.map f program.erase := by
  induction program with
  | nil => rfl
  | cons step _ ih =>
    simp only [Program.map, Program.erase, Syntax.Component.map, Syntax.Definition.mapList] at ih ⊢
    rw [ih]
    cases step with
    | core => rfl
    | command cmd => cases cmd <;> rfl

theorem mapThen (f : M → N) (preserve : ∀ {payload type}, interfaces payload = some type → targets (f payload) = some type)
    (left : Program feat profile interfaces before middle) (right : Program feat profile interfaces middle after) :
    (left.then right).map f preserve = (left.map f preserve).then (right.map f preserve) := by
  induction left with
  | nil => rfl
  | cons head _ ih => simp [Program.then, Program.map, ih]

end Silmaril.Proofs.Wasm.Component.IntrinsicWiring
