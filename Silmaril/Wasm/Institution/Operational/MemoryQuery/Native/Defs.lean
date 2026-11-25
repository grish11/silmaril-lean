module

public import Silmaril.Wasm.Institution.Operational.MemoryQuery.Defs
public import Silmaril.Wasm.Lime1.Execution.Transport
public import Silmaril.Wasm.Versions.Lime1.Runtime.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.MemoryQuery

open Silmaril.Wasm.Execution

def arg : Wasm.V1.MemArg := ⟨2, 0⟩
def index : MemIdx := ⟨0⟩

def v1Code : State → List Wasm.V1.Execution.Admin
  | .size => [.source .memorySize]
  | .load address => [.source (.intConst .i32 address), .source (.intLoad .i32 none arg)]
  | .value bits => [.source (.intConst .i32 bits)]
  | .trap => [.trap]

def limeCode : State → List Wasm.Lime1.Execution.Admin
  | .size => [.source .memorySize]
  | .load address => [.source (.intConst .i32 address), .source (.intLoad .i32 none arg)]
  | .value bits => [.source (.intConst .i32 bits)]
  | .trap => [.trap]

def coreCode : State → List Core.Admin
  | .size => [.plain (.memorySize index)]
  | .load address => [.plain (.intConst .i32 address), .plain (.intLoad .i32 none index arg.toCore)]
  | .value bits => [.plain (.intConst .i32 bits)]
  | .trap => [.trap]

def v1Config {H : Type} (s : Wasm.V1.Execution.Store H) (f : Runtime.Frame) (q : State) :
    Wasm.V1.Execution.Config H := ⟨s, f, v1Code q⟩

def limeConfig {H : Type} (s : Wasm.Lime1.Execution.Store H) (f : Runtime.Frame) (q : State) :
    Wasm.Lime1.Execution.Config H := ⟨s, f, limeCode q⟩

def coreConfig {H : Type} (s : Core.Store H) (f : Core.Frame) (q : State) : Core.Config H :=
  ⟨s, f, coreCode q⟩

end Silmaril.Wasm.Institution.Operational.MemoryQuery
