module

public import Silmaril.Wasi.Component.Accept.Ref.Defs

/-! # Component acceptors on the reference machine: the typed environment

`Ref.Accepted` lets the host invoke an exported function on *any* component values
(`EnvLabel`). A real host (wasmtime, jco) type-checks every call against the function's WIT
type, and REF's `Store.invoke` assumes that it does: on ill-typed arguments the copied
machine usually stops with an `internal` fault (`lower_flat: value does not match type`), a
violated REF precondition, not a specification trap. It does not always stop. Calling an
exported `accept: func(list<u8>) -> bool` on the ill-typed list `[u32 300, u8 1, u8 2]`
returns `true` (`Typed/Examples.lean`). Such runs are **spurious**. This module defines the
intended environment:

* `funcFT? m f`: the WIT type of the function value `f` in configuration `m`;
* `ArgsTyped ft args`: `args` have the parameter types of `ft` (`Val.HasType`, pointwise, decided
  by `Val.typeCheckList?`);
* `TypedEnvLabel m₁ es`: invoke an exported function **on arguments of its type** (its type in
  the configuration `m₁` reached by instantiation), tick, or cancel;
* `AcceptedTyped prof c w`: `Accepted` with `TypedEnvLabel` (`Thms`: it implies `Accepted`);
* `acceptLinkedProgAt ft`, `RecordsTyped ft prof c args`, `bytesOf?`, `AcceptedTypedBytes ft prof c w`:
  `accept` is supplied at type `ft`, which REF's import check makes the component's import type
  (`list<u8>` is `acceptFT`; a `tuple<u8, u8>` acceptor needs `ft` at that tuple); what `accept` received, and
  acceptance read through `bytesOf?`, the counterpart of the IR's `bytes?`. It takes one
  `list<u8>` *or* one `tuple`/`record` of `u8`. On REF a `tuple<u8, …>` acceptor receives a
  record, not a list, so `AcceptedTyped` (which matches `[list<u8> w]`) is empty on tuple
  acceptors, while `AcceptedTypedBytes` is not (`Typed/Examples.lean`). `Thms`:
  `acceptedTyped_bytes`;
* `AcceptedExportTyped prof c w`: the export `"accept"` exists, `[list<u8> w]` has its parameter
  types and its result type is `bool`, and the call after instantiation can return `true`
  (`Thms`: it implies `AcceptedExport`);
* `acceptRunTyped`: `acceptRun` that refuses (`none`) any call whose arguments do not
  type-check (`Thms`: `acceptRunTyped_sound`);
* `refTypedBytesSystem prof`: the bytes system with `AcceptedTyped`.

**Re-exported `accept` is intended, not spurious.** A component that re-exports its `accept`
import lets the host call `accept` through the component on any `list<u8>`. The call is an
import call made through the component's interface, and the IR reading
(`Silmaril.Wasi.Accept.bytesLang`, which counts calls of the import in plays of the wiring)
counts it the same way. Under the typed environment such a component accepts exactly the
byte strings the host passes (`Typed/Examples.lean`). This is a property of the component,
not of an ill-typed host.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasi.Accept.Ref

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Canon

variable {E : CoreEngine}

/-- The WIT type of function value `f` in `m`. -/
def funcFT? {σ : Type} (m : Config E σ) (f : FuncId) : Option (WIT.FuncType Empty RtId) :=
  (m.store.func? f).map CFuncInst.ft

/-- `args` have the parameter types of `ft`. -/
def argsTyped (ft : WIT.FuncType Empty RtId) (args : List Value.Val) : Bool :=
  Value.Val.typeCheckList? (ft.params.map Prod.snd) args

/-- The typed environment's moves: invoke an exported function on arguments of its type in
`m₁`, tick, or cancel. -/
def TypedEnvLabel (m₁ : Config E AcceptSt) (es : List (String × FuncId)) :
    Label E AcceptSt → Prop
  | .host (.invoke _ f args) =>
    f ∈ es.map Prod.snd ∧ ∃ ft, funcFT? m₁ f = some ft ∧ argsTyped ft args = true
  | .host .tick => True
  | .host (.cancel _) => True
  | .host (.run _) => False
  | _ => True

/-- **Acceptance in the typed environment.** -/
def AcceptedTyped [∀ a b, Decidable (E.ExternSub a b)] (prof : ProfileKind)
    (c : Syntax.Component E.Module) (w : List UInt8) : Prop :=
  ∃ tr₀ m₁ inst es tr m₂,
    Steps prof noReady dispatch initCfg (.host (.run (acceptLinkedProg c)) :: tr₀) m₁ ∧
    (∀ ev, Label.host ev ∉ tr₀) ∧
    (traceObs tr₀).findSome? decodeInstantiated? = some (inst, es) ∧
    Steps prof noReady dispatch m₁ tr m₂ ∧ (∀ l ∈ tr, TypedEnvLabel m₁ es l) ∧
    [bytesVal w] ∈ m₂.host

/-- Allocate the host function `accept` **at type `ft`** and instantiate `c` with it. REF's import
check requires `ft` to match the component's import type; `acceptLinkedProg` is the case
`ft = acceptFT` (`list<u8>`). -/
def acceptLinkedProgAt [∀ a b, Decidable (E.ExternSub a b)] (ft : WIT.FuncType Empty RtId)
    (c : Syntax.Component E.Module) : P E AcceptSt (Ret E) := do
  let f ← storeHostFunc ft ⟨0⟩
  instantiateProg c [("accept", .func f)]

/-- `args` were recorded by `accept` (supplied at type `ft`) in some run of the typed
environment. -/
def RecordsTyped [∀ a b, Decidable (E.ExternSub a b)] (ft : WIT.FuncType Empty RtId)
    (prof : ProfileKind) (c : Syntax.Component E.Module) (args : List Value.Val) : Prop :=
  ∃ tr₀ m₁ inst es tr m₂,
    Steps prof noReady dispatch initCfg (.host (.run (acceptLinkedProgAt ft c)) :: tr₀) m₁ ∧
    (∀ ev, Label.host ev ∉ tr₀) ∧
    (traceObs tr₀).findSome? decodeInstantiated? = some (inst, es) ∧
    Steps prof noReady dispatch m₁ tr m₂ ∧ (∀ l ∈ tr, TypedEnvLabel m₁ es l) ∧
    args ∈ m₂.host

/-- A `u8` component value. -/
def u8Of? : Value.Val → Option UInt8
  | .int .u8 n => if 0 ≤ n ∧ n < 256 then some n.toNat.toUInt8 else none
  | _ => none

/-- **The bytes an `accept` call carries**, read as the component IR's `bytes?` reads them: one
argument, a `list<u8>` or a `tuple`/`record` of `u8`s. -/
def bytesOf? : List Value.Val → Option (List UInt8)
  | [.list vs] => vs.mapM u8Of?
  | [.record vs] => vs.mapM u8Of?
  | _ => none

/-- **Acceptance through `bytesOf?`** in the typed environment: some recorded argument list
carries `w`. It covers `accept(list<u8>)` and fixed-arity `accept(tuple<u8, …>)`. -/
def AcceptedTypedBytes [∀ a b, Decidable (E.ExternSub a b)] (ft : WIT.FuncType Empty RtId)
    (prof : ProfileKind) (c : Syntax.Component E.Module) (w : List UInt8) : Prop :=
  ∃ args, RecordsTyped ft prof c args ∧ bytesOf? args = some w

/-- **Exported acceptance at the right type**: the export `"accept"` takes `[list<u8> w]` at its
parameter types and returns a `bool`, and the call can return `true`. -/
def AcceptedExportTyped [∀ a b, Decidable (E.ExternSub a b)] (prof : ProfileKind)
    (c : Syntax.Component E.Module) (w : List UInt8) : Prop :=
  ∃ m₁ inst es f ft,
    Silmaril.Wasm.Component.Reference.InstResult.instance m₁ inst es ∈
      Silmaril.Wasm.Component.Reference.instBehaviours prof refHost
        (Silmaril.Wasm.Component.Reference.initConfig []) c [] ∧
    es.lookup "accept" = some f ∧ funcFT? m₁ f = some ft ∧
    argsTyped ft [bytesVal w] = true ∧ ft.result = some (.prim .bool) ∧
    Silmaril.Wasm.Component.Reference.Outcome.returns (some [.bool true]) ∈
      Silmaril.Wasm.Component.Reference.callBehaviours prof refHost m₁ ⟨0⟩ f [bytesVal w]

section Exec

variable [∀ a b, Decidable (E.ExternSub a b)] (X : E.Exec) (o : Oracle E)

/-- `runCalls`, refusing calls whose arguments do not have the type the function has in
`m₁`. -/
def runCallsTyped (fuel : Nat) (m₁ : Config E AcceptSt) (es : List (String × FuncId)) :
    Nat → List (String × List Value.Val) → Config E AcceptSt → Option (Config E AcceptSt)
  | _, [], m => some m
  | k, (name, args) :: rest, m => do
    let f ← es.lookup name
    let ft ← funcFT? m₁ f
    if argsTyped ft args then
      let r ← Conformance.callUntil noReady dispatch X o (fun _ => false) (pure .unit) fuel ⟨k⟩ f
        args m
      runCallsTyped fuel m₁ es (k + 1) rest r.config
    else none

/-- `acceptRun` in the typed environment, with `accept` supplied at type `ft` (default
`list<u8>`). -/
def acceptRunTyped (fuel : Nat) (c : Syntax.Component E.Module)
    (calls : List (String × List Value.Val)) (ft : WIT.FuncType Empty RtId := acceptFT) :
    Option AcceptSt := do
  let (_, m₁) ← hostStep? noReady (.run (acceptLinkedProgAt ft c)) (initCfg (E := E))
  let r := Machine.run noReady dispatch X o fuel m₁
  let (_, es) ← (traceObs r.labels).findSome? decodeInstantiated?
  let m ← runCallsTyped X o fuel r.config es 0 calls r.config
  pure m.host

end Exec

/-- A decoded component as an acceptor in the typed environment. -/
structure RefTypedAcceptor (prof : ProfileKind) where
  /-- The component. -/
  comp : Syntax.Component Eng.Module

instance (prof : ProfileKind) : Cslib.Automata.Acceptor (RefTypedAcceptor prof) UInt8 :=
  ⟨fun a w => AcceptedTyped prof a.comp w⟩

/-- **Component binaries on the reference machine, typed environment.** -/
def refTypedBytesSystem (prof : ProfileKind) : Silmaril.Consequence.System ByteArray (List UInt8) :=
  Silmaril.Consequence.System.ofDecoder
    (fun b => (decodeValid (prof := prof) b).map fun a => (⟨a.comp⟩ : RefTypedAcceptor prof)) id

end Silmaril.Wasi.Accept.Ref
