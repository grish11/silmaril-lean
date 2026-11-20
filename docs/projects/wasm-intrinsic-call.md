# Typed direct-call entry and outcomes

`DirectCall caller parameters results` relates a caller function index to a
store address, the Wasm function there, its closed signature, and an actual
stack-indexed `Code` callee. The callee context may differ from the caller
context; its `ModuleInstOk` proof is indexed by the **same** store, not an
equality between independently constructed worlds. Arguments are indexed in
declaration order. Result stacks use the machine's top-first convention.

`DirectCall.entry` simulates actual Core `call` and `call_ref` steps into the
real administrative frame and label. The typed argument vector and integer
zero defaults erase to `Frame.forCall`. `DirectCall.run_sound` lifts real Core
steps under those two wrappers and proves value/trap outcomes with the caller
frame restored and no store mutation. After resolution the typed execution
does not test arity, operand widths, initialized locals, host-vs-Wasm code, or
address validity again. Division errors and `unreachable` still trap. Outer
`none` is fuel exhaustion, not a trap or divergence result.

This is a sound **resolved invocation adapter**, not a compiler for arbitrary
raw calls. The caller's static function type may differ by subtyping from the
instance's principal type. The next typing bridge is an explicit adapter for
that relation. Core call entry and cleanup are proved in the forward direction;
the existing machine's reflection theorem applies inside the callee, not yet
to all raw steps through administrative wrappers. Explicit `return`, branching,
host calls, indirect calls, recursion and mutable stores are outside this PR.

For recursive interop, the next representation to compare is a first-order
indexed continuation stack and a store-indexed table of typed bodies. A call
instruction names a typed entry rather than carrying or inlining its body.
Push captures the caller frame, untouched operands and result-indexed suffix;
pop reinstates the saved context. The step relation must cover return,
trap bubbling and repeated calls (including cycles) before it can implement
the address-level `FunEquiv` observer or lift linked `ModuleEquiv`/component
observations. `Code.append` only composes straight-line effects.

```sh
lake build --wfail +Silmaril.Wasm.Execution.Core.Intrinsic.Call.Thms
lake env lean -j1 -M4096 -DautoImplicit=false -E warning tests/wasm/intrinsic-machine/Call.lean
```
