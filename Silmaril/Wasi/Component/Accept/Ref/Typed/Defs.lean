module

public import Silmaril.Wasi.Component.Accept.Ref.Defs

/-! # Component acceptors on the reference machine: the typed environment

The untyped environment (`EnvPolicy.untyped`, `Accepted`) lets the host invoke an exported
function on *any* component values. A real host (wasmtime, jco) type-checks every call against
the function's WIT type, and REF's `Store.invoke` assumes that it does: on ill-typed arguments
the copied machine usually stops with an `internal` fault (`lower_flat: value does not match
type`), a violated REF precondition, not a specification trap. It does not always stop.
Calling an exported `accept: func(list<u8>) -> bool` on the ill-typed list
`[u32 300, u8 1, u8 2]` returns `true` (`Typed/Examples.lean`). Such runs are **spurious**.
The intended environment is `EnvPolicy.typed` (`Ref/Defs.lean`: `TypedEnvLabel`,
`AcceptedTyped`, `RecordsTyped`, `acceptRunTyped`, and the default `bytesSystem`). This module
adds the typed notions that are not instances of the generic policy development:

* `bytesOf?`, `AcceptedTypedBytes ft prof c w`: acceptance read through `bytesOf?`, the
  counterpart of the IR's `bytes?`, with `accept` supplied at type `ft` (`acceptLinkedProgAt`;
  REF's import check makes `ft` the component's import type, so a `tuple<u8, u8>` acceptor
  needs `ft` at that tuple). `bytesOf?` takes one `list<u8>` *or* one `tuple`/`record` of `u8`.
  On REF a `tuple<u8, …>` acceptor receives a record, not a list, so `AcceptedTyped` (which
  matches `[list<u8> w]`) is empty on tuple acceptors, while `AcceptedTypedBytes` is not
  (`Typed/Examples.lean`). `Thms`: `acceptedTyped_bytes`;
* `AcceptedExportTyped prof c w`: the export `"accept"` exists, `[list<u8> w]` has its parameter
  types and its result type is `bool`, and the call after instantiation can return `true`
  (`Thms`: it implies `AcceptedExport`).

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

end Silmaril.Wasi.Accept.Ref
