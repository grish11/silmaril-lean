module

public import Silmaril.Wasm.Game.Accept.Defs
public import Silmaril.Wasm.Behaviour.Semantics.V3.Defs

/-! # Inputs accepted by a module through an exported `accept(ptr, len) -> i32`

The export reading for core modules, next to the import reading of `Silmaril.Wasm.Game.Accept`.
The **embedding** is the standard one of a host calling a validator:

1. the module is instantiated as the specification does (`IsSpecInstance m mt I c₀`: validation,
   allocation against fresh host functions for its imports, `c₀` the `$instantiate`
   configuration), and instantiation returns (`Steps P host c₀ ⟨s₀, f₀, vals []⟩`);
2. the host writes the input into the instance's memory `0`: the store becomes
   `s₀.setMem ma ⟨mt, B⟩` for the address `ma` of that memory and any contents `B` (any size; the
   memory keeps its type);
3. the host invokes the export named `name` with `[i32 ptr, i32 len]`. The segment
   `[ptr, ptr + len)` is in the memory and does not wrap the 32-bit address space
   (`ptr + len < 2 ^ 32`).

An input is accepted when some such run returns `[i32 1]` (`exportAccepted`). It is rejected
when one returns `[i32 0]` (`exportRejected`). It is **accepted and never rejected**
(`exportAcceptedNotRejected`) when some run returns `1` and no run returns `0`; both quantifiers
range over the same runs (`exportRun`, the results of the embedding's runs on the input). The host relation `host` resolves the module's
import calls during both runs. The admitted hosts are a parameter (`Hosts`).

This is one environment class, not every context: hosts that also ran other exports first, or
that changed other state, are outside it.

New definitions (no source).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.Accept

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Game

/-- The function address of the export named `name`. -/
def exportFunc? (mi : ModuleInst) (name : String) : Option Nat :=
  (mi.exports.find? (·.name = name)).bind fun x => match x.addr with
    | .func a => some a
    | _ => none

/-- The bytes `[p, p + n)` of a memory, as a list (`none` out of bounds). -/
def memSegment (B : ByteArray) (p n : Nat) : Option (List UInt8) :=
  (Execution.Memory.readBytes B p n).map (·.data.toList)

/-- **Inputs the export `name` answers with `result` in the embedding**. -/
def exportAnswered (P : Profile) (Hosts : Set (HostSemantics Nat)) (m : Module) (name : String)
    (result : BitVec 32) : Set (List UInt8) :=
  {w | ∃ (mt : CModuleType) (I : ScalarInstance) (c₀ : Config Nat), IsSpecInstance m mt I c₀ ∧
    ∃ host ∈ Hosts, ∃ (s₀ : Store Nat) (f₀ : Frame),
      Steps P host c₀ ⟨s₀, f₀, vals []⟩ ∧
    ∃ (a ma : Nat) (mt' : MemoryType) (B₀ B : ByteArray) (p n : BitVec 32),
      exportFunc? c₀.frame.module name = some a ∧ c₀.frame.module.mems[0]? = some ma ∧
      s₀.mems[ma]? = some ⟨mt', B₀⟩ ∧ memSegment B p.toNat n.toNat = some w ∧
      p.toNat + n.toNat < 2 ^ 32 ∧
      Behaviour.returns [.i32 result] ∈
        behaviours P host (s₀.setMem ma ⟨mt', B⟩) a [.i32 p, .i32 n]}

/-- Accepted: some run of the embedding answers `1`. -/
def exportAccepted (P : Profile) (Hosts : Set (HostSemantics Nat)) (m : Module)
    (name : String) : Set (List UInt8) :=
  exportAnswered P Hosts m name 1

/-- Rejected: some run of the embedding answers `0`. -/
def exportRejected (P : Profile) (Hosts : Set (HostSemantics Nat)) (m : Module)
    (name : String) : Set (List UInt8) :=
  exportAnswered P Hosts m name 0

/-- **The runner of the export embedding**: the `i32` results of the runs on an input. -/
def exportRun (P : Profile) (Hosts : Set (HostSemantics Nat)) (m : Module) (name : String)
    (w : List UInt8) : Set (BitVec 32) :=
  {r | w ∈ exportAnswered P Hosts m name r}

/-- Some run of the embedding answers `1`, and none answers `0`. -/
def exportAcceptedNotRejected (P : Profile) (Hosts : Set (HostSemantics Nat)) (m : Module)
    (name : String) : Set (List UInt8) :=
  exportAccepted P Hosts m name ∩ (exportRejected P Hosts m name)ᶜ

end Silmaril.Wasm.Game.Accept
