module

public import Silmaril.Wasm.Component.Conformance.Run.Defs
public import Silmaril.Wasm.Component.Conformance.ToRef.Defs
public import Silmaril.Logic.Consequence.Acceptor.Defs
public import Silmaril.Wasm.Component.Reference.Defs

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

**The environment.** After instantiation the host invokes functions, ticks and cancels calls.
It runs no other host program. An *environment policy* (`EnvPolicy`) says which invokes it may
make, given the configuration `m₁` reached by instantiation and the instance's exports `es`,
and carries a Bool `check` with a soundness proof for the executable driver. There are two:

* `EnvPolicy.typed`, **the intended environment**: invoke an exported function only on
  arguments of its WIT type in `m₁` (`funcFT?`, `argsTyped`), as wasmtime and jco do;
* `EnvPolicy.untyped`: invoke an exported function on any component values. This violates
  REF's precondition for `Store.invoke` and admits spurious runs (`Ref/Typed/Examples.lean`).

`EnvPolicy.typed ≤ EnvPolicy.untyped` (`Thms`). The core engine and the component choice oracle
are arbitrary (`Steps prof …` quantifies over their steps).

**Acceptance**, once for every policy. `RecordsWith P ft prof c args`: `accept`, supplied at
type `ft` (`acceptLinkedProgAt`), records `args` in some run of the environment `P`.
`AcceptedWith P prof c w` is the `list<u8>` case: some call of `accept` receives the list `w`
of `u8`s. Acceptance is existential over environments and nondeterminism, as for modules
(`Wasm.Game.Accept`) and IR components (`Wasi.Accept.bytesLang`). A component that never calls
`accept` accepts nothing. A component that re-exports its `accept` import lets the environment
record any argument it passes. The instances: `Accepted`/`EnvLabel` (untyped) and
`AcceptedTyped`/`RecordsTyped`/`TypedEnvLabel` (typed).

**Executable side.** `acceptRunWith X o P fuel c calls ft` runs the linked instantiation, then
the top-level calls `calls` (by export name) in sequence on the interpreter `X` with oracle `o`,
refusing (`none`) any call `P.check` rejects, and returns the host state. `acceptRun` and
`acceptRunTyped` are its instances. `Thms`: `recordsWith_of_run` (every recorded argument list
is recorded in `RecordsWith`), once for every policy.

**Exported `accept`.** `AcceptedExport prof c w`: the component has no root imports, and calling
its export `accept: func(list<u8>) -> bool` on `w` right after instantiation can return `true`
(REF's `exportBehaviours`). `Thms`: `acceptedExport_of_run` proves it from an executable run
(`Embedder.instantiateRun`, `callTop`). The typed form is `AcceptedExportTyped` (`Typed`).

**Bytes.** `bytesSystemWith P prof : System ByteArray (List UInt8)`: `b ⊢ w` iff `b` decodes on
REF (`decodeRef`), validates (`Reference.check? Features.p2`), and the component accepts `w` in
environment `P` over the Core 3.0 engine `core3 neverFail`. **The default `bytesSystem` is
typed.** `bytesSystemUntyped` is the untyped one; `refBytesSystem` (untyped) and
`refTypedBytesSystem` are deprecated aliases.

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

/-- Allocate the host function `accept` **at type `ft`** and instantiate `c` with it. REF's import
check requires `ft` to match the component's import type; `acceptLinkedProg` is the case
`ft = acceptFT` (`list<u8>`). -/
def acceptLinkedProgAt [∀ a b, Decidable (E.ExternSub a b)] (ft : WIT.FuncType Empty RtId)
    (c : Syntax.Component E.Module) : P E AcceptSt (Ret E) := do
  let f ← storeHostFunc ft ⟨0⟩
  instantiateProg c [("accept", .func f)]

/-- Allocate the host function `accept: func(list<u8>)` and instantiate `c` with it as its root
import. -/
abbrev acceptLinkedProg [∀ a b, Decidable (E.ExternSub a b)] (c : Syntax.Component E.Module) :
    P E AcceptSt (Ret E) :=
  acceptLinkedProgAt acceptFT c

/-- The initial configuration: the empty store, nothing recorded. -/
def initCfg : Config E AcceptSt := Config.init CStore.empty []

/-- The WIT type of function value `f` in `m`. -/
def funcFT? {σ : Type} (m : Config E σ) (f : FuncId) : Option (WIT.FuncType Empty RtId) :=
  (m.store.func? f).map CFuncInst.ft

/-- `args` have the parameter types of `ft`. -/
def argsTyped (ft : WIT.FuncType Empty RtId) (args : List Value.Val) : Bool :=
  Value.Val.typeCheckList? (ft.params.map Prod.snd) args

/-! ## Environment policies -/

/-- The environment's moves after instantiation, given which invokes are `allowed`: an allowed
invoke, a tick or a cancel; internal steps, choices and observations are the machine's. The
host runs no other program. -/
def EnvMove (allowed : FuncId → List Value.Val → Prop) : Label E AcceptSt → Prop
  | .host (.invoke _ f args) => allowed f args
  | .host .tick => True
  | .host (.cancel _) => True
  | .host (.run _) => False
  | _ => True

/-- **An environment policy**: which top-level invokes the host may make after instantiation.
`Allowed m₁ es f args`: the host may invoke function value `f` on `args`, where `m₁` is the
configuration instantiation reached and `es` the instance's exports. `check` decides it for
the executable driver (`check_sound`). -/
structure EnvPolicy (E : CoreEngine) where
  /-- The invokes the host may make. -/
  Allowed : Config E AcceptSt → List (String × FuncId) → FuncId → List Value.Val → Prop
  /-- The executable check the driver runs before each invoke. -/
  check : Config E AcceptSt → List (String × FuncId) → FuncId → List Value.Val → Bool
  /-- The check is sound. -/
  check_sound : ∀ m₁ es f args, check m₁ es f args = true → Allowed m₁ es f args

namespace EnvPolicy

/-- The environment's moves under policy `P`. -/
abbrev Label (P : EnvPolicy E) (m₁ : Config E AcceptSt) (es : List (String × FuncId)) :
    Machine.Label E AcceptSt → Prop :=
  EnvMove (P.Allowed m₁ es)

/-- **The untyped environment**: invoke any exported function on any component values. It
admits spurious runs (`Ref/Typed/Examples.lean`). -/
def untyped : EnvPolicy E where
  Allowed _ es f _ := f ∈ es.map Prod.snd
  check _ es f _ := decide (f ∈ es.map Prod.snd)
  check_sound _ _ _ _ h := of_decide_eq_true h

/-- **The typed environment** (the intended one): invoke an exported function only on
arguments of its WIT type in `m₁` (`funcFT?`, `argsTyped`), as wasmtime and jco do. -/
def typed : EnvPolicy E where
  Allowed m₁ es f args :=
    f ∈ es.map Prod.snd ∧ ∃ ft, funcFT? m₁ f = some ft ∧ argsTyped ft args = true
  check m₁ es f args :=
    decide (f ∈ es.map Prod.snd) && (match funcFT? m₁ f with
      | some ft => argsTyped ft args
      | none => false)
  check_sound m₁ _ f _ h := by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1, by cases hf : funcFT? m₁ f <;> simp_all⟩

/-- `P ≤ Q`: every invoke `P` allows, `Q` allows. -/
instance : LE (EnvPolicy E) := ⟨fun P Q => ∀ m₁ es f args, P.Allowed m₁ es f args →
  Q.Allowed m₁ es f args⟩

end EnvPolicy

/-! ## Acceptance under a policy -/

/-- **`args` were recorded** by `accept`, supplied at type `ft`, in some run of the environment
`P`: the linked instantiation (no host moves), then moves of `P` only. -/
def RecordsWith [∀ a b, Decidable (E.ExternSub a b)] (P : EnvPolicy E)
    (ft : WIT.FuncType Empty RtId) (prof : ProfileKind) (c : Syntax.Component E.Module)
    (args : List Value.Val) : Prop :=
  ∃ tr₀ m₁ inst es tr m₂,
    Steps prof noReady dispatch initCfg (.host (.run (acceptLinkedProgAt ft c)) :: tr₀) m₁ ∧
    (∀ ev, Label.host ev ∉ tr₀) ∧
    (traceObs tr₀).findSome? decodeInstantiated? = some (inst, es) ∧
    Steps prof noReady dispatch m₁ tr m₂ ∧ (∀ l ∈ tr, P.Label m₁ es l) ∧
    args ∈ m₂.host

/-- **The bytes `c` accepts in environment `P`**: `accept: func(list<u8>)` records
`[list<u8> w]`. -/
abbrev AcceptedWith [∀ a b, Decidable (E.ExternSub a b)] (P : EnvPolicy E)
    (prof : ProfileKind) (c : Syntax.Component E.Module) (w : List UInt8) : Prop :=
  RecordsWith P acceptFT prof c [bytesVal w]

/-- The untyped environment's moves: invoke an exported function (on any arguments), tick, or
cancel. -/
abbrev EnvLabel (es : List (String × FuncId)) : Label E AcceptSt → Prop :=
  EnvMove fun f _ => f ∈ es.map Prod.snd

/-- The typed environment's moves: invoke an exported function on arguments of its type in
`m₁`, tick, or cancel. -/
abbrev TypedEnvLabel (m₁ : Config E AcceptSt) (es : List (String × FuncId)) :
    Label E AcceptSt → Prop :=
  EnvPolicy.typed.Label m₁ es

/-- **The bytes component `c` accepts in the untyped environment** (`EnvLabel`), at component
choice profile `prof`. It contains spurious runs of ill-typed hosts; `AcceptedTyped` is the
intended notion. -/
abbrev Accepted [∀ a b, Decidable (E.ExternSub a b)] (prof : ProfileKind)
    (c : Syntax.Component E.Module) (w : List UInt8) : Prop :=
  AcceptedWith EnvPolicy.untyped prof c w

/-- **Acceptance in the typed environment** (`TypedEnvLabel`), the intended notion. -/
abbrev AcceptedTyped [∀ a b, Decidable (E.ExternSub a b)] (prof : ProfileKind)
    (c : Syntax.Component E.Module) (w : List UInt8) : Prop :=
  AcceptedWith EnvPolicy.typed prof c w

/-- `args` were recorded by `accept` (supplied at type `ft`) in some run of the typed
environment. -/
abbrev RecordsTyped [∀ a b, Decidable (E.ExternSub a b)] (ft : WIT.FuncType Empty RtId)
    (prof : ProfileKind) (c : Syntax.Component E.Module) (args : List Value.Val) : Prop :=
  RecordsWith EnvPolicy.typed ft prof c args

/-! ## Exported `accept` -/

/-- The acceptor host as a reference-semantics host (specification limits and quirks). -/
def refHost : Silmaril.Wasm.Component.Reference.Host E AcceptSt :=
  { hr := noReady, impl := acceptImpl }

/-- The acceptor host with an interpreter, as an embedder. -/
def emb (X : E.Exec) : Embedder E AcceptSt := { X := X, hr := noReady, host := acceptImpl }

/-- **Exported `accept: func(bs: list<u8>) -> bool`**: instantiating `c` with no root imports
from the empty store, then calling its export `"accept"` on `list<u8> w`, can return `true`
(REF's `exportBehaviours`). -/
def AcceptedExport [∀ a b, Decidable (E.ExternSub a b)] (prof : ProfileKind)
    (c : Syntax.Component E.Module) (w : List UInt8) : Prop :=
  Silmaril.Wasm.Component.Reference.Outcome.returns (some [.bool true]) ∈
    Silmaril.Wasm.Component.Reference.exportBehaviours prof refHost [] c [] "accept" [bytesVal w]

/-! ## The executable driver -/

section Exec

variable [∀ a b, Decidable (E.ExternSub a b)] (X : E.Exec) (o : Oracle E)

/-- **The executable driver's calls under policy `P`**: the top-level calls `calls` (export
name, arguments), numbered from `k`, from `m`, after instantiation reached `m₁` with exports
`es`. A call whose export is missing, that `P.check` refuses, or that was not enabled gives
`none`. -/
def runCallsWith (P : EnvPolicy E) (fuel : Nat) (m₁ : Config E AcceptSt)
    (es : List (String × FuncId)) :
    Nat → List (String × List Value.Val) → Config E AcceptSt → Option (Config E AcceptSt)
  | _, [], m => some m
  | k, (name, args) :: rest, m => do
    let f ← es.lookup name
    if P.check m₁ es f args then
      let r ← Conformance.callUntil noReady dispatch X o (fun _ => false) (pure .unit) fuel ⟨k⟩ f
        args m
      runCallsWith P fuel m₁ es (k + 1) rest r.config
    else none

/-- **Run an acceptor in environment `P`**: the linked instantiation with `accept` at type `ft`
(at most `fuel` steps), then `calls`; the argument lists `accept` recorded. `none` if
instantiation did not report, an export is missing, `P` refuses a call, or an invoke was not
enabled. -/
def acceptRunWith (P : EnvPolicy E) (fuel : Nat) (c : Syntax.Component E.Module)
    (calls : List (String × List Value.Val)) (ft : WIT.FuncType Empty RtId := acceptFT) :
    Option AcceptSt := do
  let (_, m₁) ← hostStep? noReady (.run (acceptLinkedProgAt ft c)) (initCfg (E := E))
  let r := Machine.run noReady dispatch X o fuel m₁
  let (_, es) ← (traceObs r.labels).findSome? decodeInstantiated?
  let m ← runCallsWith X o P fuel r.config es 0 calls r.config
  pure m.host

/-- `runCallsWith` in the untyped environment (which does not read `m₁`; `m` stands for it). -/
abbrev runCalls (fuel : Nat) (es : List (String × FuncId)) (k : Nat)
    (calls : List (String × List Value.Val)) (m : Config E AcceptSt) :
    Option (Config E AcceptSt) :=
  runCallsWith X o EnvPolicy.untyped fuel m es k calls m

/-- **Run an acceptor in the untyped environment**, `accept` at `list<u8>`. -/
abbrev acceptRun (fuel : Nat) (c : Syntax.Component E.Module)
    (calls : List (String × List Value.Val)) : Option AcceptSt :=
  acceptRunWith X o EnvPolicy.untyped fuel c calls

/-- `runCalls`, refusing calls whose arguments do not have the type the function has in
`m₁`. -/
abbrev runCallsTyped (fuel : Nat) (m₁ : Config E AcceptSt) (es : List (String × FuncId)) :
    Nat → List (String × List Value.Val) → Config E AcceptSt → Option (Config E AcceptSt) :=
  runCallsWith X o EnvPolicy.typed fuel m₁ es

/-- **Run an acceptor in the typed environment**, with `accept` supplied at type `ft` (default
`list<u8>`). -/
abbrev acceptRunTyped (fuel : Nat) (c : Syntax.Component E.Module)
    (calls : List (String × List Value.Val)) (ft : WIT.FuncType Empty RtId := acceptFT) :
    Option AcceptSt :=
  acceptRunWith X o EnvPolicy.typed fuel c calls ft

end Exec

/-! ## Bytes -/

/-- The Core 3.0 engine of the executable reference machine. -/
abbrev Eng : CoreEngine := core3 Silmaril.Wasm.SingleThreaded.neverFail

/-- A component of the reference semantics, as an acceptor of bytes in environment `P` at
profile `prof`. -/
structure PolicyAcceptor (P : EnvPolicy Eng) (prof : ProfileKind) where
  /-- The component. -/
  comp : Syntax.Component Eng.Module

instance (P : EnvPolicy Eng) (prof : ProfileKind) :
    Cslib.Automata.Acceptor (PolicyAcceptor P prof) UInt8 :=
  ⟨fun a w => AcceptedWith P prof a.comp w⟩

/-- A decoded component as an acceptor in the untyped environment (`Accepted`). -/
abbrev RefAcceptor (prof : ProfileKind) : Type := PolicyAcceptor EnvPolicy.untyped prof

/-- A decoded component as an acceptor in the typed environment (`AcceptedTyped`). -/
abbrev RefTypedAcceptor (prof : ProfileKind) : Type := PolicyAcceptor EnvPolicy.typed prof

/-- Decode a component binary on REF and validate it (`Features.p2`). -/
def decodeValid {prof : ProfileKind} (b : ByteArray) : Option (RefAcceptor prof) :=
  match Conformance.decodeRef b with
  | .ok c => if (Reference.check? Features.p2 c).isOk then some ⟨c⟩ else none
  | .error _ => none

/-- **Component binaries on the reference machine, environment `P`**: `b ⊢ w` iff `b` decodes
and validates as a component that accepts `w` (`AcceptedWith P prof`, over `core3 neverFail`). -/
def bytesSystemWith (P : EnvPolicy Eng) (prof : ProfileKind) :
    Silmaril.Consequence.System ByteArray (List UInt8) :=
  Silmaril.Consequence.System.ofDecoder
    (fun b => (decodeValid (prof := prof) b).map fun a => (⟨a.comp⟩ : PolicyAcceptor P prof)) id

/-- **Component binaries on the reference machine**, the default: the typed environment
(`AcceptedTyped`). -/
abbrev bytesSystem (prof : ProfileKind) : Silmaril.Consequence.System ByteArray (List UInt8) :=
  bytesSystemWith EnvPolicy.typed prof

/-- Component binaries on the reference machine in the untyped environment (`Accepted`), which
admits spurious runs. Kept for comparison; `bytesSystem` is the intended notion. -/
abbrev bytesSystemUntyped (prof : ProfileKind) :
    Silmaril.Consequence.System ByteArray (List UInt8) :=
  bytesSystemWith EnvPolicy.untyped prof

/-- The untyped bytes system under its former name. -/
@[deprecated "use `Ref.bytesSystem` (typed environment, the default) or \
`Ref.bytesSystemUntyped` (this definition's meaning)" (since := "2026-11-16")]
abbrev refBytesSystem (prof : ProfileKind) : Silmaril.Consequence.System ByteArray (List UInt8) :=
  bytesSystemUntyped prof

/-- The typed bytes system under its former name. -/
@[deprecated bytesSystem (since := "2026-11-16")]
abbrev refTypedBytesSystem (prof : ProfileKind) :
    Silmaril.Consequence.System ByteArray (List UInt8) :=
  bytesSystem prof

end Silmaril.Wasi.Accept.Ref
