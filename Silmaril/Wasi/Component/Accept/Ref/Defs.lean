module

public import Silmaril.Wasm.Component.Conformance.Run.Defs
public import Silmaril.Wasm.Component.Conformance.ToRef.Defs
public import Silmaril.Logic.Consequence.Acceptor.Defs

/-! # Component acceptors on the reference machine: `accept(list<u8>)` from bytes

The component IR has no list types, so a component importing `accept: func(list<u8>)` does not
lower to it (`Silmaril.Wasi.Accept.defValTy_list`). The reference component machine (REF,
`Silmaril.Wasm.Component.Reference`) has the whole canonical ABI, including lists in linear
memory. It reads such binaries (`Conformance.decodeRef`) and runs their core code on a core
engine. This module defines the bytes a component accepts on REF.

**The host.** The host supplies one root import, `accept: func(bs: list<u8>)` (`acceptFT`), as
a host function value (`storeHostFunc`). When called, it reads its lifted arguments
(`on_start`), appends them to the host state (`AcceptSt`, a list of argument lists), and
resolves with no result (`on_resolve`). This is REF's synchronous `mk_host_func` pattern,
as in `Conformance.Host`. `acceptLinkedProg c` allocates that function and instantiates `c` with
it as its argument `"accept"` (REF root instantiation, `instantiateProg`).

**The environment.** After instantiation, the host may invoke any *exported* function, on any
arguments and in any order, may tick, and may cancel calls. It runs no other host program
(`EnvLabel`). The core engine and the component choice oracle are arbitrary
(`Steps prof …` quantifies over their steps).

**Acceptance** (`Accepted prof E c w`): some such run records the argument list `[bytesVal w]`,
that is, some call of the imported `accept` receives the list `w` of `u8`s. Acceptance is
existential over environments and nondeterminism, as for modules (`Wasm.Game.Accept`) and IR
components (`Wasi.Accept.bytesLang`). A component that never calls `accept` accepts nothing.
A component that re-exports its `accept` import lets the environment record any argument.

**Executable side.** `acceptRun X o fuel c calls` runs the linked instantiation, then the
top-level calls `calls` (by export name) in sequence on the interpreter `X` with oracle `o`,
and returns the host state. `Thms`: `acceptRun_sound` (every recorded byte list is accepted).

**Bytes.** `refBytesSystem prof : System ByteArray (List UInt8)`: `b ⊢ w` iff `b` decodes on
REF (`decodeRef`), validates (`Reference.check? Features.p2`), and the component accepts `w`
over the Core 3.0 engine `core3 neverFail`.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasi.Accept.Ref

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Canon

/-- The host state: the argument lists `accept` received, in order. -/
abbrev AcceptSt : Type := List (List Value.Val)

/-- `accept: func(bs: list<u8>)`. -/
def acceptFT : WIT.FuncType Empty RtId := ⟨[("bs", .list (.prim .u8))], none, false⟩

/-- The component value of a byte string: a `list<u8>`. -/
def bytesVal (w : List UInt8) : Value.Val := .list (w.map fun b => .int .u8 b.toNat)

variable {E : CoreEngine}

/-- The host function `accept`: read the arguments, record them, resolve with no result. -/
def acceptFn (_ : HostFuncId) (c : CallerId) : P E AcceptSt (Ret E) := do
  let args ← callVals (.onStart c)
  let st ← hostGet
  hostSet (st ++ [args])
  callUnit (.onResolve c (some []))
  pure (.cancel .none)

/-- The host behaviour: `accept` only. -/
def acceptImpl : HostImpl E AcceptSt := { funcs := acceptFn }

/-- No host waitable is ever ready. -/
def noReady : HostReady AcceptSt := fun _ _ => false

/-- The late-bound call dispatcher of the acceptor host (specification limits and quirks). -/
def dispatch [∀ a b, Decidable (E.ExternSub a b)] : Call E → P E AcceptSt (Ret E) :=
  Canon.dispatch Limits.spec Quirks.none noReady acceptImpl

/-- Allocate the host function `accept` and instantiate `c` with it as its root import. -/
def acceptLinkedProg [∀ a b, Decidable (E.ExternSub a b)] (c : Syntax.Component E.Module) : P E AcceptSt (Ret E) := do
  let f ← storeHostFunc acceptFT ⟨0⟩
  instantiateProg c [("accept", .func f)]

/-- The initial configuration: the empty store, nothing recorded. -/
def initCfg : Config E AcceptSt := Config.init CStore.empty []

/-- The environment's moves after instantiation: invoke an exported function, tick, or cancel;
internal steps, choices and observations are the machine's. -/
def EnvLabel (es : List (String × FuncId)) : Label E AcceptSt → Prop
  | .host (.invoke _ f _) => f ∈ es.map Prod.snd
  | .host .tick => True
  | .host (.cancel _) => True
  | .host (.run _) => False
  | _ => True

/-- **The bytes component `c` accepts** on REF, at component choice profile `prof`: some run
from the linked instantiation, then environment moves only, records `[bytesVal w]`. -/
def Accepted [∀ a b, Decidable (E.ExternSub a b)] (prof : ProfileKind)
    (c : Syntax.Component E.Module) (w : List UInt8) : Prop :=
  ∃ tr₀ m₁ inst es tr m₂,
    Steps prof noReady dispatch initCfg (.host (.run (acceptLinkedProg c)) :: tr₀) m₁ ∧
    (∀ ev, Label.host ev ∉ tr₀) ∧
    (traceObs tr₀).findSome? decodeInstantiated? = some (inst, es) ∧
    Steps prof noReady dispatch m₁ tr m₂ ∧ (∀ l ∈ tr, EnvLabel es l) ∧
    [bytesVal w] ∈ m₂.host

/-! ## The executable driver -/

section Exec

variable [∀ a b, Decidable (E.ExternSub a b)] (X : E.Exec) (o : Oracle E)

/-- The top-level calls `calls` (export name, arguments), numbered from `k`, from `m`. -/
def runCalls (fuel : Nat) (es : List (String × FuncId)) :
    Nat → List (String × List Value.Val) → Config E AcceptSt → Option (Config E AcceptSt)
  | _, [], m => some m
  | k, (name, args) :: rest, m => do
    let f ← es.lookup name
    let r ← Conformance.callUntil noReady dispatch X o (fun _ => false) (pure .unit) fuel ⟨k⟩ f
      args m
    runCalls fuel es (k + 1) rest r.config

/-- **Run an acceptor**: the linked instantiation (at most `fuel` steps), then `calls`; the
argument lists `accept` recorded. `none` if instantiation did not report, an export is missing
or an invoke was not enabled. -/
def acceptRun (fuel : Nat) (c : Syntax.Component E.Module)
    (calls : List (String × List Value.Val)) : Option AcceptSt := do
  let (_, m₁) ← hostStep? noReady (.run (acceptLinkedProg c)) (initCfg (E := E))
  let r := Machine.run noReady dispatch X o fuel m₁
  let (_, es) ← (traceObs r.labels).findSome? decodeInstantiated?
  let m ← runCalls X o fuel es 0 calls r.config
  pure m.host

end Exec

/-! ## Bytes -/

/-- The Core 3.0 engine of the executable reference machine. -/
abbrev Eng : CoreEngine := core3 Silmaril.Wasm.SingleThreaded.neverFail

/-- A component of the reference semantics, as an acceptor of bytes at profile `prof`. -/
structure RefAcceptor (prof : ProfileKind) where
  /-- The component. -/
  comp : Syntax.Component Eng.Module

instance (prof : ProfileKind) : Cslib.Automata.Acceptor (RefAcceptor prof) UInt8 :=
  ⟨fun a w => Accepted prof a.comp w⟩

/-- Decode a component binary on REF and validate it (`Features.p2`). -/
def decodeValid {prof : ProfileKind} (b : ByteArray) : Option (RefAcceptor prof) :=
  match Conformance.decodeRef b with
  | .ok c => if (Reference.check? Features.p2 c).isOk then some ⟨c⟩ else none
  | .error _ => none

/-- **Component binaries on the reference machine**: `b ⊢ w` iff `b` decodes and validates as a
component that accepts `w` (`Accepted prof`, over `core3 neverFail`). -/
def refBytesSystem (prof : ProfileKind) : Silmaril.Consequence.System ByteArray (List UInt8) :=
  Silmaril.Consequence.System.ofDecoder (decodeValid (prof := prof)) id

end Silmaril.Wasi.Accept.Ref
