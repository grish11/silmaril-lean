# Components as consequence checkers

A component can be read as a consequence relation `X → C → Prop` between assumptions `x` and
statements `c`. This development defines four protocols over the component event traces of
`Silmaril.Wasi.Accept` (`Traces σ`, named events `WEv`). It keeps three things apart:

- the **Prop consequence**: some play answers `yes` (`Accepted`), with a play witness
  (`AcceptWitness`, which erases to `Accepted` under `Nonempty`);
- the **execution-model status**: an SZS problem over completed queries (`execProblem`), using
  the definitions in `Silmaril.Logic.Szs`;
- **soundness and completeness** against a target system (`Sound`, `Complete`).

New definitions; the SZS statuses follow `szs-success`, and `szs-2007` for the 2007 text.

## Modules

| Module | Contents |
| --- | --- |
| `Silmaril.Wasi.Component.Consequence.{Defs,Thms}` | `Answer` (`yes`, `no`, `trap`, `other`), `Boundary` (`call`, `answer`), `Reading X C`, `Accepted`, `AcceptWitness`, `Answered`, `Sound`, `Complete`, `execProblem`, `classify`, `StatusPair`/`status`, host classes (`HostFn`, `hostAdmissible`, `ForallHosts`, `ExistsHost`), `Step`, `Policy` (`list`, `finset`, `count`, `named`, `namedFirst`), `Policy.Hom` (`listToFinset`, `listToCount`, `listToNamed`), `epochState`, `epoch`, and the protocol readings `exportCheck`, `exportStateful`, `importAssert`, `importStateful`. |
| `Silmaril.Wasi.Component.Consequence.Checkers.{Defs,Thms}` | Specification strategies for protocol 1: `answerChecker`, `emptyChecker`, `silentChecker`, `memberChecker`, and concrete `list<u32>`/`u32` instances (`memberU32`, `emptyU32`, `u32Dec`). |
| `Silmaril.Wasi.Component.Consequence.Stateful.{Defs,Thms}` | A specification strategy for protocol 2: `statefulMember` (`axiom`, `check`, `reset`), and the `u32` instance `statefulMemberU32`. |
| `Silmaril.Wasi.Component.Consequence.Matrix.{Defs,Examples}` | The interpretation matrix: protocol × state policy × boundary (48 cells, 24 supported). Each cell names its reading, its theorems as checked names, and its evidence. `gaps` lists what no cell provides. |

## Protocols and observation boundaries

| Protocol | Reading | Observed |
| --- | --- | --- |
| Exported `check(ax, stmt) -> bool` | `exportCheck f dec` | at the return of `check`: `true` is `yes`, `false` is `no` (a successful false), a trap is `trap`, and anything else is `other` |
| Exported `axiom(v)` / `check(stmt) -> bool`, optional `reset()` | `exportStateful b fns P decA decC` | `axiom` and `reset` at `b` (the call, or a non-trapping return); `check` at its return |
| Imported `assert(ax, stmt)` | `importAssert b f dec` | at `.call`, the request (always `yes`); at `.answer`, the host's answer (`trap` if the host traps) |
| Imported `assume(v)` / `assert(stmt)`, optional `reset()` | `importStateful b fns P decA decC` | everything at `b` |

Divergence is not an answer. The plays are finite, so a call that never returns has no return
event. `Silmaril.Games` has infinite plays, but they are not used here.

The plays of a component range over every host and every caller, so `Accepted` is existential
over both. Restricting the traces to a host class shrinks it (`accepted_mono`,
`existsHost_accepted`). `ForallHosts H` implies `ExistsHost H` only when `H` is nonempty
(`forallHosts_existsHost`); over the empty class it holds vacuously (`forallHosts_empty`).

## State and epochs

The stateful protocols fold the steps of the current epoch with a named update policy. `list`
appends in order and keeps duplicates. `finset` inserts. `count` counts (`Nat`). `named` stores
keyed assumptions `K × V` into `K → Option V`, last write wins, and `namedFirst` keeps the first
write. A reset starts a new epoch (`epochState_append_reset`).

No structural rule is assumed of any reading. A component may answer differently for permuted
or duplicated assumptions. The bridges between policies take closure of the *target* as a
hypothesis:

- `accepted_stateful_hom` maps accepted queries along a policy morphism;
- `sound_hom` transports soundness when the target is invariant on the morphism's fibres;
- `finset_sound_of_mem_closed` does so for lists to finite sets, assuming exchange, contraction
  and duplication;
- `sound_perm_closure` does so for permuted assumptions, assuming permutation closure.

## Execution status: acceptance is SAT, not THM

In `execProblem T r x c`, the interpretations are completed queries `(prefix, event)`. The models
of `Ax` are the completed queries `(x, c)` of `T`, and the models of `C` are those answering
`yes`.

- `accepted_iff_sat`: existential acceptance is `Current.SAT`.
- `THM` is the universal reading: every completed query, under every host and caller, answers
  `yes` (`execProblem_thm_iff`).
- **Honest empty models**: when no query completes, the status is `CAX` and `THM` holds
  vacuously (`thm_of_cax`). This happens without acceptance (`exists_thm_not_accepted`,
  `thm_silentChecker`). `THM` implies acceptance only when some query completes
  (`accepted_of_thm`).
- `classify` is a restricted four-way partition of this execution model into `CAX`, `STH`, `SCT`
  and `NOC`. It does not replace the SZS ontology. It is classical (`noncomputable`), the status
  it picks holds (`classify_holds`), and accepted queries are exactly those classified `STH` or
  `NOC` (`accepted_iff_classify`).
- The 2007 text has no `STH`. Current `STH` is the 2007 `SAT ∧ THM` (`sth_iff_v2007`).
- An import claim observed at `.call` has no countermodel (`importAssert_call_thm`). It is never
  classified `SCT` or `NOC`.

## Specification checkers

| Component | Relation | Execution status |
| --- | --- | --- |
| `emptyChecker` / `emptyU32` | empty (`not_accepted_emptyChecker`) | `SCT`: every query completes with `false` (`status_emptyChecker`, `status_emptyU32`) |
| `silentChecker` | empty (`not_accepted_silentChecker`) | `CAX`: nothing completes, and `THM` holds vacuously (`status_silentChecker`, `thm_silentChecker`) |
| `memberChecker` / `memberU32` | exactly `c ∈ xs`, sound and complete (`accepted_memberChecker`, `accepted_memberU32`, `memberChecker_sound`, `memberChecker_complete`) | `STH` if `c ∈ xs`, else `SCT` (`status_memberU32`) |

| `statefulMember` / `statefulMemberU32` (protocol 2, `list` policy, `.call` boundary) | exactly `c ∈ xs`, where `xs` is the list of the current epoch's assumptions (`accepted_statefulMember`, `accepted_statefulMemberU32`) | `STH` if `c ∈ xs`, else `SCT` (`status_statefulMember`) |

The stateful checker answers each call immediately, from the state of its generating play. If
a caller interleaves calls of another shape, those calls stay pending (unanswered); they are
never answered differently.

These are **specification strategies** (`Strategy.generate`), Lean definitions of their plays.
The theorems are about these strategies only.

## Gentzen sequents from UNSAT and TAUTO checkers

`Silmaril.Wasi.Component.Consequence.Gentzen.{Defs,Thms}` covers a component that exports a
list checker `f(list<T>) -> bool` (`listCheck`). It gives a predicate on lists (`checkerOf`),
which can be read two ways as a Gentzen sequent relation (`Silmaril.Consequence.Gentzen`):

- `unsatSeq` (`viaUnsat`): `Γ ⊢ Δ` iff the component accepts `Γ ++ Δ.map neg`.
- `tautSeq` (`viaTauto`): `Γ ⊢ Δ` iff it accepts `Γ.map neg ++ Δ`.

The adapter theorems take soundness of the component as a hypothesis:

- `unsatSeq_le_valid` needs `CheckSound` and `NegComplete`.
- `tautSeq_le_valid` needs `TautSound` and `NegSound`.
- The Gentzen closures (`derives_*`) and the completeness directions are covered too.

Over signed formulas, satisfaction is the core `Gentzen.signedSat`, and the sign flip satisfies
both negation laws (`Gentzen.signedSat_negSound`, `Gentzen.signedSat_negComplete`). The former
local names `signedSat`, `signed_negSound` and `signed_negComplete` remain as deprecated
forwarding names. The specification **clash checker** `clashU32` accepts exactly the lists
containing some `x` and `-x`. It is sound both as an UNSAT checker and as a TAUTO checker, for
different reasons, so both of its readings are valid. Its UNSAT reading is `Reflexive`. Its
execution status for a list (`STH` or `SCT`) is about plays, not the SZS status of the formula.

## Signed and two-sided protocols

`Silmaril.Wasi.Component.Consequence.Signed.{Defs,Thms}` reads three more protocols as lists of
signed formulas or as Gentzen sequents.

- **Imported `pos(v)`, `neg(v)`, `done()`, optional `reset()`** (`importBatch`). Each `done`
  claims the batch emitted since startup, the previous `done`, or the last `reset`. The batch is
  the state *before* the `done`, and `done` then starts the next one. A trailing batch with no
  `done` is never emitted. At `Boundary.call` the reading records the component's requests; at
  `Boundary.answer` it records only non-trapping host answers. The two are different projections
  and agree only under hypotheses on the hosts. Whether a trapped `done` closes the batch is the
  explicit `TrapDone` policy.
  - `batchUnsat` and `batchTaut` are the raw Gentzen UNSAT and TAUTO readings of the batches.
    Their validity needs a soundness hypothesis on the emitter and the matching negation law
    (`batchUnsat_le_valid`, `batchTaut_le_valid`).
  - `batchFinset` is an existential finite-set reading (some emitted list has these members).
    Soundness transfers to it (`batchFinset_unsat`); equality with the list reading would need
    invariance hypotheses that are not assumed.
- **Exported `check(conj: list v, disj: list v) -> bool`** (`seqCheck`, `seqOf`); its signed
  variant is the same reading over `Signed W`.
  - Core modules are read through an explicit, partial byte codec (`coreSeq`), with the profile
    and host set as separate runtime quantifiers.
  - Through `memberEnc`, `MemberCheck` derives exactly `Γ ⊢ [c]` with `c ∈ Γ`: sound for every
    host set, and exact below the ABI bound for a nonempty host set (`coreSeq_member_sound`,
    `coreSeq_member_iff`). It encodes no other succedent, so it is not complete for them.
  - `EmptyCheck` derives nothing (`coreSeq_empty`).
- **Exported `assume(v)`, `assert(v)`, `check() -> bool`, optional `reset()`**
  (`exportAssumeAssert`, `pairSeqOf`). Both sides accumulate, `reset` starts a new epoch, and the
  snapshot a `check` reads is explicit (`SnapshotAt.ret` or `.call`). `assert` names an
  observation that adds to the succedent, not a proof.

Specification components for these protocols (`Silmaril.Wasi.Component.Consequence.Signed.Spec`;
specification strategies, not compiled components):

- `batchEmitter enc L`: on `run`, emits the literals of a batch of `L` through `pos`/`neg` and
  calls `done`. At the call boundary its batches are exactly `L` (`batches_batchEmitter`). If
  every batch of `L` is unsatisfiable, its UNSAT reading is valid
  (`batchUnsat_batchEmitter_le_valid`).
- `idChecker`: an exported `check(conj, disj)` over signed `u32` lists that answers whether the
  two lists share a formula (`seqOf_idChecker`). It is `Gentzen.Reflexive` and valid for every
  satisfaction relation (`reflexive_idChecker`, `idChecker_le_valid`).

## Interpretations

`Silmaril.Wasi.Component.Consequence.Interp.{Defs,Thms}` exposes the readings as core
interpretations (`Silmaril.Consequence.Interp`). An interpretation reads a value under a typed
configuration as a system, or returns `none`.

- **Trace sets.** `batchInterp`, `seqInterp`, `assumeAssertInterp` and `assumeAssertSeqInterp`
  are always defined. Their configurations hold only static choices: function names, boundary,
  trap policy, snapshot. How callers and hosts behave is the set of plays, not configuration.
  `ofTraces` reads strategies through their traces.
- **Core modules.** `coreInterp` reads a module AST, and `coreBytesInterp` decodes bytes first.
  `CoreConfig` holds the profile, the admissible host set, the export name and the byte codec.
  - The bytes of `MemberCheck` decode and, under `memberConfig`, give a system that is sound
    against single-succedent membership for every host set (`member_sound`). It is complete on
    the slice `Γ.length + 1 < 2 ^ 32` for a nonempty host set (`member_completeOn`).
  - The bytes of `EmptyCheck` give `some ⊥`, a verified empty system (`coreBytesInterp_empty`).
  - Bytes that do not decode give `none`, which is not a system (`coreBytesInterp_nil`).

## Scope and gaps

- No compiled component binary implements any protocol. The catalog's `compiledComponent` shape
  is unsupported, and no compilation correctness is claimed.
- **One core module**: `Silmaril.Wasm.Examples.EmptyCheck` is the empty checker as a core
  module. Its export `check(ptr, len) -> i32` is `i32.const 0`, verified against Core execution,
  with its 45-byte binary. It accepts nothing (`exportAccepted_eq_empty`) and rejects every input
  shorter than `2 ^ 32` (`exportRejected_eq`). As a `System` under any byte encoding, it is `⊥`.
- **A nonempty core module**: `Silmaril.Wasm.Examples.MemberCheck` is the finite membership
  checker. It is a 108-byte module whose `check(ptr, len)` scans `c :: as` once and returns
  whether `c ∈ as`. It is verified against Core execution, with total correctness (the loop
  variant is `len - i`). Its acceptance is exact: `exportAccepted_eq` is `memberLang` below
  `2 ^ 32`, and `exportRejected_eq` is the complement. As a relation on byte lists it is
  exactly membership (`accepted_iff_mem`), so it is `Reflexive` and the least such relation
  (`accepted_le_of_reflexive`). Statements and assumptions are single bytes.
- **No component wraps a core module.** Connecting `EmptyCheck` to the component reading
  `exportCheck` would need a canonical-ABI correspondence between `list<u8>` arguments and
  `(ptr, len)`, like `CanonLowerAccept`. Nothing here assumes one.
- Only protocol 2, with the `list` policy at the `.call` boundary, has a specification
  component. The other stateful cells, and all of protocol 4, have general laws only.
- `Silmaril.Wasi.Component.Consequence.Bridge.Thms` connects these readings to
  `Silmaril.Logic.Consequence`:
  - `Accepted T r` is a `System`, and `AcceptWitness T r` is a `WSystem` erasing to it
    (`erase_acceptWitness`).
  - The closure hypotheses are the named structural rules: `Exchange`
    (`sound_perm_closure_of_exchange`) and `WeakSubset` (`finset_sound_of_weakSubset`).
  - The membership checker is the least `Reflexive` relation (`reflexive_memberChecker`,
    `memberChecker_sound_of_reflexive`).

## Checking

```sh
lake build Silmaril.Wasi.Component.Consequence.Thms \
  Silmaril.Wasi.Component.Consequence.Checkers.Thms \
  Silmaril.Wasi.Component.Consequence.Stateful.Thms \
  Silmaril.Wasi.Component.Consequence.Gentzen.Thms \
  Silmaril.Wasi.Component.Consequence.Signed.Thms \
  Silmaril.Wasi.Component.Consequence.Signed.Spec.Thms \
  Silmaril.Wasi.Component.Consequence.Matrix.Examples
```
