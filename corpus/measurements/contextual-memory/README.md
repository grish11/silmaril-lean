# Experimental state-sensitive C/ELF obligations

`Silmaril.Project.Shapes.Contextual` retains initial Core memory, initial machine
memory, caller-visible final observations, write bounds and ABI return obligations.
This supplements the existing scalar-only shapes. It does not widen their claims.

A context supplies entries and observations, not a refinement validity law.
`Obligation` separately requires joint source/machine entries for **every** input,
safety of every admitted actual Core entry, a machine first-return execution and
matching actual Core final states for every machine first-return outcome. It
also requires ABI preservation and the declared write bound. It does not prove
all-path termination on a nondeterministic machine. Local callee contract obligations have
separate source safety/postconditions and machine strict contracts, with explicit
nonempty entries; they never replace the actual Core bodies or machine steps.
No callee refinement is assumed. Callee contracts are conjunctive obligations,
not implication premises; an impossible local contract cannot erase the caller
result obligation. The current instance has zero callees.

## Actual OpenSSL global-memory instance

`Silmaril.Elf.Corpus.OpenSslSecureInitialized.Thms` binds the real
`CRYPTO_secure_malloc_initialized` enabled-secure-memory source fragment in
OpenSSL 3.5.9 `crypto/mem_sec.c` to frontend typed Ail and kernel-checked Core
elaboration. Four source-span equations retain the declaration, function header,
enabled return and closing brace. An actual frontend guard checks the quoted Ail.
This adapter selects the enabled preprocessor branch; it is **not** a checked
full translation-unit preprocessor. Correspondence to the recorded canonical
`generated/x86_64/include/openssl/configuration.h` remains build provenance.

The selected canonical x86_64 libcrypto function has address `0x1eab70`, size7,
and reads the four-byte local global at `0x48c278`. Kernel byte equations check
actual instructions and the dynamic symbol/name records; the displacement
arithmetic is checked. These are **not a whole-file ELF parse or CodeAt theorem**.
The remaining canonical libcrypto whole-file gap is unchanged.

The input is every 32-bit pattern interpreted as a signed C int. Core starts with
one real allocated signed-int object, bound to the exact elaborated global symbol.
The initial machine global must encode that same value, at load bias zero. The
entry requires actual loaded code, a System V call/return stack and readable
global bytes. The observation compares signed return, global contents, Core
allocation/byte/lifetime preservation and stdout preservation. Read diagnostics
`lastUsed` and `currentLocation` are intentionally unobserved. The machine may
write no memory; its callee-saved registers and return ABI must be preserved.
There are no asynchronous mutations, threads, heap inputs or external calls in
this context. No environment-event/trace equivalence is claimed.

`Task.compiles_to` is an actual, unproved state-sensitive obligation. Its joint
entry existence and Core safety clauses are obligations, not proved facts.
The scalar registry remains9functions/9statements plus6binary statements; this
**one experimental memory-context statement is tracked separately**, pending
configuration-adapter and full ELF placement integration. Semantic proofs:0.

Reproduce (dependencies per repository toolchain):

```
LEAN_NUM_THREADS=2 lake build --wfail \
  Silmaril.Project.Shapes.Contextual.Thms \
  Silmaril.Elf.Corpus.OpenSslSecureInitialized.Thms
```

The included final replay receipt hashes each touched module, source, canonical
ELF and generated configuration. Only these modules' derived cache files were
cleared; dependencies stayed warm. `cache=unspecified` reflects that mixed state.
Axiom inspection found only propext/Classical.choice/Quot.sound for elaboration
and symbol selection; byte and source-span equations require no axioms.

## Feature/blocker matrix

| Family/function | Actual binding/status | Remaining boundary |
|---|---|---|
| OpenSSL `CRYPTO_secure_malloc_initialized` | Actual frontend/Core; global read/state observations; experimental unproved obligation | Enabled-branch adapter provenance, whole-file placement gap; no semantic proof |
| Existing mimalloc version and OpenSSL QUIC leaves | Published scalar-context statements | No globals/calls/heap contract coverage from those statements |
| TinyCC five classifiers | Published scalar/conditional actual source/Core statements | Integer-only; no memory beyond parameter objects |
| mimalloc `_mi_os_page_size`, `_mi_os_has_overcommit`, `_mi_os_has_virtual_reserve`, `_mi_bin_size` | Blocked; no new coverage | Struct/member/array memory, target size_t representation, globals and configuration |
| cJSON pointer/type predicates | Blocked; no new coverage | Struct-field loads, pointer comparison and bitwise mask elaboration/backend |
| Reference crypto buffer routines | Blocked; no new coverage | Pointer/array byte memory, loops, bitwise shifts and modular arithmetic |
| SQLite `ROUND8`/configuration-dependent helpers | Blocked; no new coverage | Correct active preprocessor definition, bitwise/size_t semantics |
| Any external-call representative | Framework only; zero instantiated call contexts | Pin actual callee source/program and code, relate call entry/effects, discharge honest local contracts |
| AArch64 functions | ELF structural work only | No AArch64 execution semantics/context instantiation |

This is a bounded feature sample, not a complete classification of all corpus functions.

Additional finite Core LTS regression: `tests/cerberus/SourceGlobalContext.lean`
executes the bound getter for 0,1,INT_MAX,INT_MIN,-1. Each returns its actual
stored global after82transitions and preserves the checked bytes/lifetime/stdout.
Removing the allocation produces the port's explicit `Unsupported` outcome
(`outside allocation lifetime UB mapping`), not an invented defined result or
an assertion that this diagnostic is a proved C UB classification. Run with
`lake env lean -DwarningAsError=true --run tests/cerberus/SourceGlobalContext.lean`.
These six observations are not semantic proofs or all-input safety evidence.
