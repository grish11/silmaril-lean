module

public import Silmaril.Wasm.Institution.Operational.CallResolution.Defs
public import Silmaril.Wasm.Lime1.Execution.Transport
public import Silmaril.Wasm.Versions.Lime1.Runtime.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime (Frame)

def v1Code : State → List Wasm.V1.Execution.Admin
  | .call i => [.source (.call i)]
  | .invoke a => [.invoke a]

def limeCode : State → List Wasm.Lime1.Execution.Admin
  | .call i => [.source (.call i)]
  | .invoke a => [.invoke a]

def v1Config {H : Type} (s : Wasm.V1.Execution.Store H) (f : Frame) (a : State) :
    Wasm.V1.Execution.Config H := ⟨s, f, v1Code a⟩

def limeConfig {H : Type} (s : Wasm.Lime1.Execution.Store H) (f : Frame) (a : State) :
    Wasm.Lime1.Execution.Config H := ⟨s, f, limeCode a⟩

/-- At the chosen index, a local function address resolves to an allocated store
entry. Core requires the entry to read its function type. -/
def Allocated {H : Type} (s : Wasm.Lime1.Execution.Store H) (f : Frame) (i : FuncIdx) : Prop :=
  ∀ a, f.module.funcs[i.toNat]? = some a → (s.funcs[a.value]?).isSome

end Silmaril.Wasm.Institution.Operational.CallResolution
