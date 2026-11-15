module

public import Silmaril.Wasm.Game.Untyped.Defs
public import Silmaril.Wasm.Execution.Memory
public import Silmaril.Formats.Accept.Defs

/-! # Inputs accepted by a core Wasm module through an `accept` import

A core module *accepts* the bytes `w` when, in some execution against some environment, it
calls its imported function `accept(ptr: i32, len: i32)` while its memory holds `w` at
`[ptr, ptr + len)`. The definition reuses the Core 3.0 semantics of the game development:

* the module is instantiated as the specification does (`IsSpecInstance m mt I c₀`: validation,
  allocation against fresh host functions, one per import, with host code the import index;
  `c₀` runs segment initialisation and the start function);
* it runs under `UStep P L`, Core reduction in product with an untyped environment `L`
  (`Silmaril.Wasm.Game.Untyped`) that answers every host call (any import, not only `accept`)
  with a new store and result;
* when a run has finished, the environment may invoke any export with arguments typed in the
  current store (`Execution.Core.InvokeOk`); instantiation must have returned first
  (`Session`).

**Observations** (`Callout`): when the running code is at a host-call redex
(`SingleThreaded.decompose?`), the callout records the import's `(module, name)`, the raw
arguments and the bytes of the instance's memory `memIdx` (the canonical ABI's `memory`
option; `0` by default) at the moment of the call. `Callouts P Envs memIdx m` is the set of
callouts reachable in some session, for some environment in the class `Envs`, after some
instantiation. Every set below is read off it, so **callout equivalence**
(`CalloutEquiv`: equal callout sets) is the observational equivalence acceptance respects;
it is exactly the equivalence under which every decoder accepts the same values
(`Silmaril.Wasm.Game.Accept.calloutEquiv_iff`).

**Decoders** read an accepted value off a callout:

* `Callout.bytes32`: arguments `[i32 ptr, i32 len]`, the bytes of the memory at
  `[ptr, ptr + len)`; an out-of-bounds segment, a missing memory or other arguments observe
  nothing (the canonical ABI traps there). `Callout.bytes64` is the `memory64` form
  (`[i64 ptr, i64 len]`, `CanonicalABI.md`'s `ptr_type` `i64`).
* `Callout.i32`, `Callout.i64`: one `i32` (resp. `i64`) argument, as `UInt32` (`UInt64`).

The accepted sets `bytesLang`, `bytes64Lang`, `i32Lang` and `i64Lang` are `accepted` with
these decoders; `accepted dec imp` is the general form for any decoder (an extension point for
canonical-ABI lifts of other types).

**Environments.** `Envs : Store Nat → SEnv UImp → Prop` picks the admitted environments given
the instantiated store; the default `UEnvOk` (`Silmaril.Wasm.Game.Untyped`) admits every
environment whose answers satisfy Core's host contract (a typed store extending the caller's,
a typed result). The specification lets a host function change memory contents, so with any
import called before `accept` the accepted set may be every byte string of the right length;
a smaller class (for instance hosts that leave memory unchanged) gives a smaller set, by
`callouts_mono`.

Scope: core modules whose imports are all functions (`IsSpecInstance`); module and memory
imports are outside this definition (`IsSpecInstanceAt` would admit them). Acceptance is a may
property of finite runs: divergence and traps after the call do not matter.

New definitions (no source); the semantics are those of `Silmaril.Wasm.Game.Untyped` and
`Silmaril.Wasm.Game.SpecInst`.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.Accept

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Game Silmaril.Formats.Accept

/-! ## Sessions -/

/-- A run has finished: its code is a Core result. In the instantiation phase (`false`) it must
have returned values (instantiation succeeded); afterwards any result (values, trap, uncaught
exception) ends an export call, and the instance remains usable. -/
def Finished : Bool → Config Nat → Prop
  | false, c => ∃ vs, c.code = (Result.values vs).toAdmin
  | true, c => ∃ r : Result, c.code = r.toAdmin

/-- **Sessions** of an instance: from the instantiation configuration `c₀` and the environment
state `q₀`, Core steps in product with the environment `L`; after a finished run, an invocation
of an export address `a ∈ addrs` with arguments typed in the current store. The flag records
whether instantiation has finished. -/
inductive Session (P : Profile) (L : SEnv UImp) (c₀ : Config Nat) (q₀ : L.S) (addrs : List Nat) :
    Bool → Config Nat × L.S → Prop where
  /-- The instantiation configuration. -/
  | start : Session P L c₀ q₀ addrs false (c₀, q₀)
  /-- A step of the product semantics (a Core step, or a host answer or divergence). -/
  | step {b : Bool} {x y : Config Nat × L.S} (h : Session P L c₀ q₀ addrs b x)
      (st : UStep P L x y) : Session P L c₀ q₀ addrs b y
  /-- The environment invokes an export after a finished run. -/
  | invoke {b : Bool} {c : Config Nat} {q : L.S} {a : Nat} {args : List Val}
      (h : Session P L c₀ q₀ addrs b (c, q)) (fin : Finished b c) (ha : a ∈ addrs)
      (ok : InvokeOk c.store a args) :
      Session P L c₀ q₀ addrs true (invoke c.store a args, q)

/-! ## Callouts -/

/-- An observed call of an import. -/
structure Callout where
  /-- The import called: its `(module, name)`. -/
  imp : String × String
  /-- The raw arguments. -/
  args : List Val
  /-- The bytes of the instance's memory at the time of the call (`none` without a memory). -/
  mem : Option ByteArray

/-- The configuration `c` of an instance of `m` is calling an import, observed as `o`, where
`memAddr` is the store address of the instance's memory. -/
def CalloutOf (m : Module) (memAddr : Option Nat) (c : Config Nat) (o : Callout) : Prop :=
  ∃ (E : Ctx) (fa h : Nat), decompose? c.store c.code = some (E, fa, h, o.args) ∧
    (m.imports[h]?).map (fun i => (i.moduleName, i.name)) = some o.imp ∧
    o.mem = (memAddr.bind fun a => c.store.mems[a]?).map MemInst.bytes

/-- **The reachable callouts of a module**: over every instantiation, every environment of the
class `Envs` and every session. -/
def Callouts (P : Profile) (Envs : Store Nat → SEnv UImp → Prop) (memIdx : Nat) (m : Module) :
    Set Callout :=
  {o | ∃ (mt : CModuleType) (I : ScalarInstance) (c₀ : Config Nat), IsSpecInstance m mt I c₀ ∧
    ∃ (L : SEnv UImp) (q₀ : L.S), Envs I.store L ∧
    ∃ (b : Bool) (c : Config Nat) (q : L.S), Session P L c₀ q₀ I.addrs b (c, q) ∧
      CalloutOf m c₀.frame.module.mems[memIdx]? c o}

/-- **Callout equivalence**: the same reachable callouts. -/
def CalloutEquiv (P : Profile) (Envs : Store Nat → SEnv UImp → Prop) (memIdx : Nat)
    (m m' : Module) : Prop :=
  Callouts P Envs memIdx m = Callouts P Envs memIdx m'

/-! ## Decoders and accepted sets -/

namespace Callout

/-- An `i32` argument. -/
def i32? : Val → Option (BitVec 32)
  | .num ⟨.int .i32, x⟩ => some x
  | _ => none

/-- An `i64` argument. -/
def i64? : Val → Option (BitVec 64)
  | .num ⟨.int .i64, x⟩ => some x
  | _ => none

/-- Exactly two arguments, each read by `f`. -/
def args2 {β : Type} (f : Val → Option β) : List Val → Option (β × β)
  | [a, b] => do return (← f a, ← f b)
  | _ => none

/-- Exactly one argument, read by `f`. -/
def args1 {β : Type} (f : Val → Option β) : List Val → Option β
  | [a] => f a
  | _ => none

/-- The bytes at `[ptr, ptr + len)` of the observed memory, if in bounds. -/
def segment (o : Callout) (ptr len : Nat) : Option (List UInt8) := do
  let mem ← o.mem
  (Execution.Memory.readBytes mem ptr len).map (·.data.toList)

/-- `accept(ptr: i32, len: i32)`: the bytes at `[ptr, ptr + len)` of the memory. -/
def bytes32 (o : Callout) : Option (List UInt8) := do
  let (p, n) ← args2 i32? o.args
  o.segment p.toNat n.toNat

/-- `accept(ptr: i64, len: i64)` (`memory64`): the bytes at `[ptr, ptr + len)`. -/
def bytes64 (o : Callout) : Option (List UInt8) := do
  let (p, n) ← args2 i64? o.args
  o.segment p.toNat n.toNat

/-- `accept(x: i32)`. -/
def i32 (o : Callout) : Option UInt32 := (args1 i32? o.args).map UInt32.ofBitVec

/-- `accept(x: i64)`. -/
def i64 (o : Callout) : Option UInt64 := (args1 i64? o.args).map UInt64.ofBitVec

end Callout

/-- The default import: `"env" "accept"`. -/
def acceptImport : String × String := ("env", "accept")

/-- **The values a module accepts** through the import `imp`, read by the decoder `dec`. -/
def accepted {α : Type} (dec : Callout → Option α) (P : Profile)
    (Envs : Store Nat → SEnv UImp → Prop) (memIdx : Nat) (imp : String × String) (m : Module) :
    Lang α :=
  {a | ∃ o ∈ Callouts P Envs memIdx m, o.imp = imp ∧ dec o = some a}

/-- **The byte language of a module**: the memory segments passed to `accept(ptr: i32, len: i32)`
(memory `0`, environments satisfying the host contract). -/
def bytesLang (P : Profile) (m : Module) (imp : String × String := acceptImport) : ByteLang :=
  accepted Callout.bytes32 P UEnvOk 0 imp m

/-- The byte language through `accept(ptr: i64, len: i64)` on a 64-bit memory. -/
def bytes64Lang (P : Profile) (m : Module) (imp : String × String := acceptImport) : ByteLang :=
  accepted Callout.bytes64 P UEnvOk 0 imp m

/-- The `i32` values passed to `accept(x: i32)`. -/
def i32Lang (P : Profile) (m : Module) (imp : String × String := acceptImport) : Lang UInt32 :=
  accepted Callout.i32 P UEnvOk 0 imp m

/-- The `i64` values passed to `accept(x: i64)`. -/
def i64Lang (P : Profile) (m : Module) (imp : String × String := acceptImport) : Lang UInt64 :=
  accepted Callout.i64 P UEnvOk 0 imp m

end Silmaril.Wasm.Game.Accept
