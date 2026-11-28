module

public import Silmaril.Wasm.Institution.Operational.MemoryWrite.Defs
public import Silmaril.Wasm.Institution.Operational.MemoryQuery.Native.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.MemoryWrite

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime (Frame MemAddr MemInst)

def v1ConfigAt {H : Type} (immediate : Wasm.V1.MemArg) (s : Wasm.V1.Execution.Store H) (f : Frame) (a : MemAddr) (m : MemInst) :
    State → Wasm.V1.Execution.Config H
  | .store address word => ⟨s, f, [.source (.intConst .i32 address), .source (.intConst .i32 word),
      .source (.intStore .i32 none immediate)]⟩
  | .written bytes => ⟨Wasm.V1.Execution.setMemory s a { m with data := bytes }, f, []⟩
  | .trap => ⟨s, f, [.trap]⟩

def limeConfigAt {H : Type} (immediate : Wasm.V1.MemArg) (s : Wasm.Lime1.Execution.Store H) (f : Frame) (a : MemAddr) (m : MemInst) :
    State → Wasm.Lime1.Execution.Config H
  | .store address word => ⟨s, f, [.source (.intConst .i32 address), .source (.intConst .i32 word),
      .source (.intStore .i32 none immediate)]⟩
  | .written bytes => ⟨Wasm.Lime1.Execution.setMemory s a { m with data := bytes }, f, []⟩
  | .trap => ⟨s, f, [.trap]⟩

def coreConfigAt {H : Type} (immediate : Wasm.V1.MemArg) (s : Core.Store H) (f : Core.Frame) (a : Nat) (m : Core.MemInst) :
    State → Core.Config H
  | .store address word => ⟨s, f, [.plain (.intConst .i32 address), .plain (.intConst .i32 word),
      .plain (.intStore .i32 none MemoryQuery.index immediate.toCore)]⟩
  | .written bytes => ⟨s.setMem a { m with bytes := bytes }, f, []⟩
  | .trap => ⟨s, f, [.trap]⟩

abbrev v1Config {H : Type} := v1ConfigAt (H := H) MemoryQuery.arg
abbrev limeConfig {H : Type} := limeConfigAt (H := H) MemoryQuery.arg
abbrev coreConfig {H : Type} := coreConfigAt (H := H) MemoryQuery.arg

/-- An entered V1 function frame with its implicit function label. The scalar
result type fixes the native arity, and the caller's operands and tail stay
outside the callee. -/
def v1ActivationCode (result : Option NumType) (callee : Frame)
    (saved : List Execution.Runtime.Value) (tail body : List Wasm.V1.Execution.Admin) :
    List Wasm.V1.Execution.Admin :=
  let arity := result.toList.length
  Wasm.V1.Execution.values saved ++ .frame arity callee [.label arity [] body] :: tail

/-- An entered Lime1 activation with its implicit result label. The arity can
describe the full ordered result list. Caller operands and code remain outside. -/
def limeActivationCode (arity : Nat) (callee : Frame)
    (saved : List Execution.Runtime.Value) (tail body : List Wasm.Lime1.Execution.Admin) :
    List Wasm.Lime1.Execution.Admin :=
  Wasm.Lime1.Execution.values saved ++ .frame arity callee [.label arity [] body] :: tail

/-- The allocated slot selected by the module's zero index has a 32-bit address type. -/
def CoreMemory32 {H : Type} (s : Core.Store H) (f : Core.Frame) (a : Nat) (m : Core.MemInst) : Prop :=
  s.mem? f MemoryQuery.index = some (a, m) ∧ m.type.address = .i32

end Silmaril.Wasm.Institution.Operational.MemoryWrite
