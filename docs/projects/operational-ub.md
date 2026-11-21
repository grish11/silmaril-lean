# Operational semantics with an explicit UB policy

`Silmaril.Semantics.Operational.Policy.Thms` is an unlabelled, relational
interface for steps and finite observations. `OpSem` contains no UB. `WithUB`
adds a predicate, not a trap or a set of fabricated outcomes. `HasOpSem` is a
value with a relation from programs to initial states and a `WithUB` model.
For function entries the program can be arguments to a resolved function; for
modules it can be a module with its imports; for components it can include the
environment and entry request. Multiple versions or profiles can select
different values for the same syntax. There is no global typeclass instance or
requirement to compare dialects by inclusion.

## What is compared

- `May` is a finite path (possibly empty) to a supplied observation.
  `TrapReachable` selects the trap tag. `UBReachable` instead reaches a
  state satisfying the explicit UB predicate. A machine can have both kinds of
  reachable path. `SafeAt` rules out *every* UB path, not just UB in one run.
- A terminal model supplies an observation and satisfies `TerminalDiscipline`.
  A normal state need not be terminal or observed; it can be a blocked or
  incomplete model. `Diverges` requires an infinite path of actual steps.
  Neither a missing observation nor the absence of a step means UB.
- `Sound` and `Complete` compare ordinary steps and observations pointwise
  in opposite directions. `AgreeWhenSafe` compares them on states safe in
  both models and proves equality of reachable finite observations at such
  starts. `DetFrom` requires at most one next state and at most one immediate
  observation at each reachable state, not progress or unique initialization.
- `OpSim left right R` matches a left step by a right finite path and preserves
  finite observations and possible UB left-to-right. Consequently right safety
  implies left safety. Equality is the identity relation; composition uses
  relational composition. Empty matches do not transport divergence. For
  `push`/`quotient`, the stronger one-step readback on every fibre does transport
  divergence as well as finite outcomes and safety.
- `Included` orders the three primitive relations covariantly. Pointwise
  intersection and union are its meet and join; union of steps can introduce
  mixed paths, so this is not an order on maximal runs or a union of may sets.
  `SafeRefines implementation specification` instead says that at inputs where
  the specification is safe, the implementation stays safe and introduces no
  new finite observations. It does not promise progress or must-behaviour.

## Policy and transport

`enforce good` suppresses ordinary behaviour at inadmissible sources, marks
them UB, and retains the steps *into* them. Its safety iff checks both original
safety and admission of all original reachable states. Under that admission
condition it preserves exactly the may-outcomes. The predicate can be the
intersection of actual typing, a feature/profile invariant and an encoding
admission contract; each invariant needs proof for the corresponding claim.

`restrict good` instead drops crossing steps; it reflects runs only with the
step-closure premise. An injective `lift` embeds that smaller system and tags
the complement as UB without inventing a success or a trap. Its steps,
observations and safety read back on the image. `restrict_lift_may_iff` gives
equality with the original larger system on a step-closed subset. A general
state `push` is an existential image, not a deterministic map of runs: an
incompatible map can splice paths at a shared state. `Compatible` requires
each representative to match a step in its fibre to the same target fibre,
and to agree on observation and UB predicates. This also applies to the
canonical map into a quotient. The cell regression demonstrates both a
subset-crossing write (UB for every value at least four) and a false result
from an incompatible map that forgets the stored value.

## Core and its boundaries

`Intrinsic.OpSem.Thms` compares the independent, stack-indexed integer/local
evaluator with actual host-free Core `Step` and `Result` at `profile oracle`.
The raw policy uses `ConfigOk` at the same result interface as the erasure;
all raw prefixes from typed starts satisfy it. `State.may_iff` matches finite
outcomes in both directions, including checked division traps, and
`State.typed_deterministic` applies only to the typed machine. The raw profile
has joinable, not unique, trap propagation steps. `Completion` uses
`Except Nat (List Val)`: an uncaught Core exception is a non-trap completion
carrying `.error`, not a successful `.ok` result. The intrinsic slice cannot
construct exceptions. See [the normalization proofs](wasm-intrinsic-machine.md#finite-run-readback-and-the-typing-ub-policy).

`DirectCall.opSem` instantiates `HasOpSem` for body entry after resolution. The
existing `DirectCall.invokeOk_iff` and `DirectCall.invoke_behaviours` already
cover accepted integer arguments and observation of the actual Core invocation
with its administrative wrappers. The regression uses the same resolved
division function for the Core call and the typed entry. In the handwritten
raw mixed-stack regression, the proof names three intermediate configurations
and four context steps; the typed version uses `runFor_sound` once after the
code and frame are built. The generic policy adds observation proofs, not an
alternative validator or a new numeric evaluator.

The landed module validator is separate (`ModuleParts.validate?_sound` after
the syntax split); `Core.Module.safe` uses `ModuleOk`, typed imports and
`HostOk` for preservation and progress. `HostOk` requires an outcome for typed
calls, not a return. Core `callRefHostDiv` represents a declared divergent
host outcome by a self-loop; a missing host outcome supplies no such step or
result. `behavioursOf` collects terminal results and infinite traces, not a
synthetic UB outcome for missing observations. The single-threaded component
presentation has a `callout` to be answered by the embedder, not a UB event.

The [games](games.md) and [component suites](component-semantics.md) already
offer labelled moves, silent transitions, waiting, divergence and distinct
session/trace observations. In particular `Simple` and `Linked2` have concrete
adequacy results under their own conditions; intrinsic wiring's
`Program.sound` is a validation theorem. This change does not port those
proofs or erase observer moves: finite may equality alone does not preserve
waiting, must-behaviour, fairness, or linking. Modules and components are
abstract clients of `HasOpSem`, not new instantiated typed machines.

### A one-memory application

`Silmaril/Wasm/Execution/Core/MemoryProfile/Defs.lean` adds an independent,
stack-height-indexed tape for `i32.const`, `i32.add`, `i32.load` and `i32.store`.
It erases to actual Core, with a fixed frame, no locals/imports, and a single
one-page memory32 at index/address zero. Load and store are full-width, with
alignment exponent and offset zero. These immediates satisfy the static
numeric bounds and the actual `MemArgOk` judgment; that is not a binary
round-trip theorem. `ConfigOk` separately checks the typed stack, frame and
memory instance. A dynamic access of four bytes tests the current byte
length in natural numbers; an encodable address can still trap.

`MemoryProfile/Thms.lean` characterizes each active memory `Core.Step` in
both directions. The evaluator reuses Core's byte primitives but recurses on
its own typed tape, not Core's reduction relation. The proof accounts for
all alternate trap bubbling prefixes, applies Core preservation, and uses
host-free confluence for terminal readback (including the final bytes).
`reach_iff` compares finite guarded Core prefixes with raw Core; `may_iff`
compares their finite return/trap observations with the evaluator. This is
not equality of administrative traces. `not_diverges` is a separate theorem.

The regression proves and runs an add/store/load round trip and both OOB
traps, and distinguishes an actually well-typed, executable `memory.size`
from the profile's intentional UB at that instruction. The main proof cost
is the boundary: matching Core's head decomposition and trap contexts,
proving typing/admission preserved, and reading back normal forms. No second
byte model is needed.

`MemoryProfile.opSem` instantiates `HasOpSem` for `MemoryProfile.Program`,
not for arbitrary functions, modules or components. With the independent
profile family available, a follow-up can label this checked adapter with
`Silmaril.Wasm.Profiles.Wasm3` without claiming that it runs arbitrary
`Profiles.Body` or `Profiles.Module` programs. Those need a translation and
proof relating their entry states and observations. This slice imports no
ISA-track code. Full-Core control/recursive continuations, hosts,
version-specific binary encodability, FX comparability, and observer-preserving
module/component linking remain outside this proof.

```sh
lake build --wfail +Silmaril.Semantics.Operational.Policy.Thms +Silmaril.Wasm.Execution.Core.Intrinsic.OpSem.Thms
lake env lean -DwarningAsError=true tests/semantics/operational-policy/Regression.lean
lake env lean -DwarningAsError=true tests/wasm/intrinsic-machine/OpSem.lean
lake env lean -DwarningAsError=true tests/wasm/intrinsic-machine/Call.lean
make check CHECK_TARGETS=+Silmaril.Wasm.Execution.Core.MemoryProfile.Thms
```
