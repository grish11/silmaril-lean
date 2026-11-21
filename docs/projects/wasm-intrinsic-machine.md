# Intrinsic integer machine for Core Wasm

`Silmaril.Wasm.Execution.Core.Intrinsic.Defs` is an executable, stack-indexed
machine for `i32` and `i64` binary operators, `local.get` of initialized integer
locals, `nop`, `drop`, and `unreachable`. It runs *inside* an already instantiated
frame. Its code is not a second Core validator, a Wasm module format, or an
alternative to `Validation.Intrinsic.Module`.

```text
Code locals input output  +  Values input  +  LocalFrame world locals
                                     │      step? / runFor
                                     ▼
                            State world locals output
                                     │      exact erasure
                                     ▼
                            Execution.Core.Config H
```

- `Op` is one instruction with an input and output stack index. `Code.seq`
  shares the intermediate index, and `Code.append` composes fragments and
  erases to raw list append. Stack indices are top-first; erasure reverses
  that order to match Core's value-instruction prefix. Declaration order is
  unchanged for locals.
- `Values` stores width-correct operands. A `Slot` is a typed local reference;
  its 32-bit source-index bound is checked once at construction. Execution
  needs neither operand count/type checks, a successful raw local lookup, nor
  local initialization tests. `Slot.get` still traverses the local list.
- `World H context` carries the actual `StoreOk` and `ModuleInstOk` facts for
  one fixed raw store and module instance. The machine neither mutates that
  store nor compares stores across contexts. `State.sound` proves the actual
  `ConfigOk` judgment, including for a pending trap; `Code.sound` proves the
  actual `InstrsOk` judgment.
- Core still traps on signed overflow, division/remainder by zero, and
  `unreachable`. Trap formation preserves the surrounding operands and code;
  the next typed step discards them. Raw Core can discard a smaller region
  first, so the reflection theorem allows one extra raw bubble. Neither
  theorem suppresses or moves trap formation.

## Exact claims

`State.step_sound` erases each typed step to **one** existing Core `Step` for
every numeric profile and host relation. `State.run_reflect` gives the exact
successor from all raw steps out of running states in the deterministic,
host-free profile. `State.step_reflect` also covers pending traps, allowing the
one extra raw step described above. This is reflection **from the image of
erasure**, not a lift of every well-typed raw configuration. `State.result_sound`
connects successful observation to Core's terminal code for values or trap,
and proves that this code cannot step in the host-free semantics.

The machine does not cover value-producing source constants (initial values
are already operands), local writes, memory, references, float/SIMD, structured
control, calls or returns. `unreachable` admits several intermediate stack
indices for the same dead suffix; the sequence is not canonical on that syntax.
The earlier intrinsic AST equivalence quotients by exact erasure and has a
noncomputable inverse; the runtime state simulation here is a different claim.

## Reproduce and compare

```sh
lake build --wfail +Silmaril.Wasm.Execution.Core.Intrinsic.Normalize.Thms
lake env lean -DwarningAsError=true tests/wasm/intrinsic-machine/Regression.lean
```

The regression checks the exact same raw `Steps` proposition twice for a mixed
stack, two local reads, unsigned division, and `nop`. The handwritten raw proof
names three intermediate configurations, supplies both lookups and the numeric
redex, and threads four context steps. With the typed construction already in
hand, the proof is one application of `State.runFor_sound`. This is a proof
construction comparison, not a runtime benchmark. It also checks exact trap
formation, partial raw trap bubbling, divide-by-zero, signed overflow,
unreachable, rejected ill-typed operands/local references, and theorem axioms.

For IR interop, indexed sequencing is the current composition interface. A
recursive extension would suspend at a typed function reference and carry a
separate indexed continuation stack for call/return. It would not use `append`
as a recursive call, insert higher-order host callbacks, or skip the existing
`call`/`call_ref` and administrative-frame rules. A first extension should use
closed, direct calls with initialized numeric locals and preserve the module
address lookup and result arity before broadening to labels or mutable stores.

## Finite-run readback and the typing UB policy

`Intrinsic.Normalize.Thms` proves that every intrinsic state finishes for some
fuel. Every reachable normal form of actual host-free Core in the deterministic
profile is exactly an erased finished state (`State.raw_normal_iff`). There is
also an iff for its result, including traps (`State.raw_result_iff`). Arbitrary
finite raw prefixes continue to the common normal form (`State.raw_prefix_finishes`);
this does not identify partial administrative states with typed states. The
existing `State.step_reflect` accounts for a raw partial trap bubble by allowing
one extra administrative step. Core reduction is not a function even under the
deterministic profile. The proof of absence of divergence reuses the argument
from the direct-invoke proof: a competing administrative step shrinks the code.
Uniqueness of normal forms by itself would not suffice.

Core has no explicit UB constructor or rule. This adapter uses
`typingUB types cfg := ¬ ConfigOk cfg types`, for a fixed result interface.
`State.raw_typed` uses the landed preservation theorem to cover **all** raw
prefixes of an erased typed state, including partial trap bubbles. To discharge
the totality premise of `HostOk` the proof embeds the host-free path into the
divergence-only host, using only the preservation conclusion; the compared runs
remain host-free. Checked divide-by-zero reaches a typed trap, not UB; too little
fuel gives no result even when the raw execution is proved nondivergent.
An empty result stack at a one-result interface is rejected by Core typing,
independently of whether it has another step. This policy is not an assertion
that other kinds of faults, inputs or host behaviour are typed or UB-free.
