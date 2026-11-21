# Closed integer/global Core execution

`Silmaril.Wasm.Execution.Core.GlobalProfile` checks a fixed, import-free entry
with exactly one `i32` global at index/address zero. Integer constants and
binary arithmetic are allowed. Globals have two typed entry variants: `.const`
admits reads only; `.var` admits reads and writes. There are no calls, host
answers, memory, exported aliases, allocation, or module initialization in
this experiment. In particular, `.var` is a closed **stateful** variant, not a
purity claim; callers comparing runs must include the initial global, and
store-sensitive observers must retain the final global. This is not a new ISA
registration or an extension to the strict-functional Closure/FX dialects.

`Code.eval` is independent of `Core.Step`. The proofs construct actual Core
steps for reads, writes and checked integer arithmetic, including contextual
trap bubbling. The erasure typechecks in the real store, frame and instruction
judgments. Running with `opSem` uses actual `Entry.policy`, not the evaluator's
graph. The restricted `Program` controls admission; arbitrary raw states outside
the instruction fragment are not automatically marked UB by this instance.
The raw typing gate uses genuine `ConfigOk` with the chosen output stack type.
Core's raw reduction of an immutable write exists, but it is not a typed tape.

For **every** `Numerics.Profile` (including either `Profile.spec nd`) and
`noHost`, `finishes_iff` relates all finite outcomes from these starts to the
same evaluator result, final frame and mutated store. It transfers raw paths to
the deterministic profile using `ConfigFree`; it does not equate individual
administrative steps with interpreter operations. `safe_and_may` proves no
reachable typing UB and exact finite observations, including traps. The
separate `not_diverges` proof transfers entire infinite paths and rules them
out using host-free normalization. The regression writes 42, then either reads
it back or divides by zero; both runs retain 42 in the final store. It also
checks computation with an immutable global and rejects a typed immutable write.

This is separate from the landed one-page, no-grow memory profile. General
fixed-size memory still needs a page-count parameter with a valid memory32
type, a byte-length witness `size = pages * pageSize`, and preservation of
that witness across admitted stores. Accesses must still use the *current* byte
length for dynamic traps; encodable offsets or a valid memory type do not
establish that an access is in bounds.
