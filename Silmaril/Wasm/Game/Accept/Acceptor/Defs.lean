module

public import Silmaril.Wasm.Game.Accept.Reject.Defs

/-! # Module acceptors: a module with distinguished imports

`ModuleAcceptor` packages a core module with the choices that make it a byte acceptor:

* the semantics profile;
* the distinguished `accept(ptr, len)` import;
* an optional `reject(ptr, len)` import;
* the memory that `ptr` addresses, and its address width (`i32` or `i64`);
* the admitted environments.

Three languages come from these choices:

* `lang`: the bytes accepted by some run;
* `neverRejectedLang`: the bytes no run rejects (everything when there is no reject import);
* `strictLang`: their intersection.

`ModuleAcceptor` is a CSLib `Acceptor` over bytes, accepting `lang`.

New definitions (no source).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.Accept

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Formats.Accept

/-- The segment decoder of an address width: `accept(ptr: i32, len: i32)` or its `memory64`
form. -/
def segmentDecoder : AddrType → Callout → Option (List UInt8)
  | .i32 => Callout.bytes32
  | .i64 => Callout.bytes64

/-- The exclusive length bound of an address width: `2 ^ 32` or `2 ^ 64`. -/
def addrBound : AddrType → Nat
  | .i32 => 2 ^ 32
  | .i64 => 2 ^ 64

/-- **A core module with distinguished `accept` and `reject` imports.** -/
structure ModuleAcceptor where
  /-- The semantics profile. -/
  profile : Profile
  /-- The module. -/
  module : Module
  /-- The accepting import. -/
  accept : String × String := acceptImport
  /-- The rejecting import, if any. -/
  reject : Option (String × String) := none
  /-- The memory addressed by the pointers. -/
  memIdx : Nat := 0
  /-- The address width of that memory. -/
  addr : AddrType := .i32
  /-- The admitted environments. -/
  envs : Store Nat → SEnv UImp → Prop := UEnvOk

namespace ModuleAcceptor

variable (A : ModuleAcceptor)

/-- The bytes accepted by some run. -/
def lang : ByteLang :=
  accepted (segmentDecoder A.addr) A.profile A.envs A.memIdx A.accept A.module

/-- The bytes no run rejects (every string, without a reject import). -/
def neverRejectedLang : ByteLang :=
  match A.reject with
  | none => ⊤
  | some r => neverRejected (segmentDecoder A.addr) A.profile A.envs A.memIdx r A.module

/-- Accepted by some run and rejected by none. -/
def strictLang : ByteLang := A.lang ⊓ A.neverRejectedLang

/-- A module acceptor is a CSLib acceptor of its language. -/
instance : Cslib.Automata.Acceptor ModuleAcceptor UInt8 := ⟨fun A w => w ∈ A.lang⟩

end ModuleAcceptor

end Silmaril.Wasm.Game.Accept
