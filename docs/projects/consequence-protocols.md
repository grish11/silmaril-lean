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

These are **specification strategies** (`Strategy.generate`), Lean definitions of their plays.
The theorems are about these strategies only.

## Scope and gaps

- No compiled component binary implements any protocol. The catalog's `compiledComponent` shape
  is unsupported, and no compilation correctness is claimed.
- No core module implements `check(ax, stmt)` with a proof against Core execution. The reading
  for one would be `Silmaril.Wasm.Game.Accept.exportAccepted`, through a canonical-ABI
  correspondence like `CanonLowerAccept`. Nothing here assumes such a correspondence.
- There is no specification component for the stateful protocols yet. Their readings have
  general laws only.
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
  Silmaril.Wasi.Component.Consequence.Matrix.Examples
```
