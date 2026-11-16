module

public import Silmaril.Wasm.Abstract.AcceptWasm.Defs
public import Silmaril.Wasm.Game.Accept.Export.Defs

/-! # The export embedding through the abstract function semantics: definitions

The embedding of `Silmaril.Wasm.Game.Accept.Export` (instantiate the module as the
specification does, write the input into memory `0`, call the export `name` on `[i32 ptr,
i32 len]`), with its admitted calls made explicit, so that each call can be run through the
abstract function `wasmFun` of `Silmaril.Wasm.Abstract.Function`:

* `ExportCall`: one admitted call. It records
  * the host relation `host`;
  * the function address `addr` of the export;
  * the **host-written store** `store = s₀.setMem ma ⟨mt', B⟩`, where `s₀` is the store after
    instantiation returns, `ma` the address of memory `0`, `mt'` its type (unchanged) and `B`
    its new contents (any size);
  * the arguments `ptr`, `len`, with the segment `[ptr, ptr + len)` in `B` and
    `ptr + len < 2 ^ 32`;
  * the `input`, the bytes of that segment.
* `exportCalls P Hosts m name`: the admitted calls. The instantiation is the spec one
  (`IsSpecInstance`), and the host is in `Hosts`.
* `absExportRun P Hosts m name w`: **the abstract runner**, the endings (`End`) of the abstract
  function `wasmFun P host addr` called on `ExportCall.args` from the one store `store`, over
  the admitted calls with input `w`.
* `retI32 r`: the endings that return the single value `i32 r`, the observation encoding of the
  embedding's answers (`1` accepts, `0` rejects; traps, divergence, exceptions and other
  results are neither).

`wasmFun` has no import interface (`Sig.empty`): the host relation resolves the module's import
calls inside the call, as in the concrete embedding.

New definitions (no source).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Abstract.Accept

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Game
open Silmaril.Wasm.Game.Accept Silmaril.Wasm.Abstract Silmaril.Games.Abstract

/-- **One admitted call of the export embedding.** -/
structure ExportCall where
  /-- The host relation resolving import calls. -/
  host : HostSemantics Nat
  /-- The function address of the export. -/
  addr : Nat
  /-- The store after instantiation, with memory `0` rewritten by the host. -/
  store : Store Nat
  /-- The pointer argument. -/
  ptr : BitVec 32
  /-- The length argument. -/
  len : BitVec 32
  /-- The bytes `[ptr, ptr + len)` of memory `0`. -/
  input : List UInt8

/-- The arguments of the call. -/
def ExportCall.args (e : ExportCall) : List Val := [.i32 e.ptr, .i32 e.len]

/-- **The admitted calls**: spec instantiation, a host of `Hosts`, the input written into
memory `0`, an in-bounds non-wrapping segment. -/
def exportCalls (P : Profile) (Hosts : Set (HostSemantics Nat)) (m : Module) (name : String) :
    Set ExportCall :=
  {e | ∃ (mt : CModuleType) (I : ScalarInstance) (c₀ : Config Nat), IsSpecInstance m mt I c₀ ∧
    e.host ∈ Hosts ∧ ∃ (s₀ : Store Nat) (f₀ : Frame), Steps P e.host c₀ ⟨s₀, f₀, vals []⟩ ∧
    ∃ (ma : Nat) (mt' : MemoryType) (B₀ B : ByteArray),
      exportFunc? c₀.frame.module name = some e.addr ∧ c₀.frame.module.mems[0]? = some ma ∧
      s₀.mems[ma]? = some ⟨mt', B₀⟩ ∧ e.store = s₀.setMem ma ⟨mt', B⟩ ∧
      memSegment B e.ptr.toNat e.len.toNat = some e.input ∧ e.ptr.toNat + e.len.toNat < 2 ^ 32}

/-- **The abstract runner**: the endings of `wasmFun` over the admitted calls on `w`. -/
def absExportRun (P : Profile) (Hosts : Set (HostSemantics Nat)) (m : Module) (name : String)
    (w : List UInt8) : Set (End (Store Nat) (List Val ⊕ Nat)) :=
  {x | ∃ e ∈ exportCalls P Hosts m name, e.input = w ∧
    x ∈ endRun (wasmFun P e.host e.addr) {e.store} e.args}

/-- The endings returning the single value `i32 r`. -/
def retI32 (r : BitVec 32) : Set (End (Store Nat) (List Val ⊕ Nat)) :=
  endToBehaviour ⁻¹' {Behaviour.returns [.i32 r]}

end Silmaril.Wasm.Abstract.Accept
