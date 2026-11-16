# Wasm problem solvers (`wasm-vc solve | drive | dag | lean`)

`tools/wasm-vc` solves small *Wasm problems*: properties of one or more linked core Wasm
modules, stated in a TOML file or as annotations in a WAT file. The reduction of x86-64
functions ([wasm-sim-reduction.md](wasm-sim-reduction.md), [wasm-sim-abi.md](wasm-sim-abi.md)) produces such problems.
This page is the reference for the problem format, the verdicts and what they rely on.

The canonical engine is the symbolic executor under `tools/wasm-vc/src/sym/`. The older i32
pipeline behind `wasm-vc vcs | smt | gen | agent` (`wat.rs`, `term.rs`, `vc.rs`, `smt.rs`,
`lean.rs`, for the spec library entries of [wasm-spec-library.md](wasm-spec-library.md)) is
deprecated but maintained: `wasm-vc gen` regenerates the committed `tactic+script` modules byte for
byte. `wasm-vc reflect` drives the reflective generator `Silmaril.Wasm.Auto.VCGen`
([wasm-binaryen-tooling.md](wasm-binaryen-tooling.md)).

## Commands

| command | does |
|---|---|
| `wasm-vc solve P [--solver z3\|cvc5\|bitwuzla] [--timeout S] [--json] [--out F] [--unroll N]` | solve one problem (`.toml`, or annotated `.wat`) |
| `wasm-vc drive DIR [-j N] [--filter S]` | solve every problem under `DIR`, respecting `deps`, and print a table |
| `wasm-vc dag DAG.json [--out F]` | solve the Wasm leaves of a `silmaril.wasm-sim.dag.v0` DAG and write verdicts and evidence back |
| `wasm-vc lean P.wat [--out F] [--check]` | generate a Lean statement and proof attempt (`wat_spec!`, `wpc`) for an annotated WAT problem |

`--root DIR` (global) names the Lean project for commands that run Lean; by default it is the
nearest ancestor directory with a `lakefile.toml`. Work files go to `target/wasm-vc/`.

## Problem TOML (`wasm-vc.problem.v1`)

Top-level keys (all optional unless marked):

| key | meaning |
|---|---|
| `schema` | `"wasm-vc.problem.v1"`. Optional; another value prints a warning and the file is read as v1 |
| `kind` (required) | `equiv`, `post` or `bmc` (below) |
| `name`, `description` | name (default: file stem) and free text |
| `deps` | names of problems this one depends on (for `drive`) |
| `modules` | `[{ name, wat }]`: modules instantiated in order (`.wat` or `.wasm`, relative to the problem); later modules' imports from `name` link to it; the last is the *main* instance |
| `entry` | function of the main instance to call once (export name, `$name` or index) |
| `calls` | call sequence instead of `entry`: `[{ func, args = [...], repeat = 1 }]`; `func` may be `inst:func`; `args` are SMT-LIB literals or parameter names |
| `a`, `b` | the two sides of an `equiv` problem, each `{ modules, entry, calls, keep }` (`modules`/`entry`/`calls` at top level are shorthand for side `a`) |
| `params` | free parameters `[{ name, ty }]` (`i32`, `i64`, `bvN`); default: the entry's parameters `p0`, `p1`, ... |
| `init` | `symbolic` (arbitrary initial globals and memories; default for `equiv`/`post`) or `module` (the module's initial values; default for `bmc`) |
| `keep` (in a side) | byte ranges `mK:OFF:N` that keep their module-initialised contents under a symbolic start (e.g. a simulator's tables) |
| `pre`, `post` | SMT-LIB formulas (lists, conjoined); names below |
| `defines` | SMT-LIB `define-fun`, `define-fun-rec`, `declare-fun` used by formulas |
| `map`, `map_from` | `equiv`: `[{ name, a, b }]` pairs of observations that must agree before and after; `map_from` reads further `[[map]]` entries from a TOML file |
| `observe` | `equiv`: subset of `result`, `trap`, `hist`, `map`, `globals`, `memory` (default `result trap hist map`) |
| `unchanged_b`, `frame_b` | `equiv`: observations of side `b` that must not change; `{ mem = "mK", except = ["OFF:N", ...] }`: memory `K` of side `b` unchanged outside the listed ranges |
| `no_trap` | `post`/`bmc`: the run must not trap |
| `never_call` | `post`/`bmc`: `[{ import = "mod.name" (trailing `*` = prefix), unless = "..." }]` |
| `contracts` | callee contracts replacing imports: `[{ import, name, pre, post, style = "values"\|"x86", params, results }]` |
| `mem_obs` | memory read by `(memN a)` in formulas: `env` or an imported memory `module.name` |
| `env` | `{ mem = "opaque"\|"array", data = [{ addr, file \| hex }] }`: model of the `mem.*` imports (below) |
| `loops` | loop annotations `[{ func, loop, invariant, decreases, parts, measures }]` (`loop` = pre-order index in `func`) |
| `infer` | infer invariants for unannotated loops of the entry (default `true`) |
| `cases` | case split: parameter to values (list, or `"lo..hi"` inclusive); one execution per combination |
| `domains` | finite domains (same syntax), handled inside one execution as an `ite` over the values |
| `unroll`, `depth` | loop unrolling bound (default 4) and call inlining depth (default 32) |
| `batch` | try all goals in one query first (default `true`) |
| `solver`, `timeout` | default solver and per-goal timeout in seconds (default `z3`, 60) |
| `expect` | expected verdict, for regression tests |

Unknown keys are errors.

**Names in formulas.** `g.NAME` is a global of the main instances at the start, `post.g.NAME`
after the run, `result` / `resultK` the results, and parameters are named as declared. On
`equiv` sides the names are prefixed `a.` / `b.`. In loop invariants, locals are named by their
WAT names, `old.NAME` is a local's value at function entry and `g.NAME` a global. With `mem_obs`,
`|mem!old|` and `|mem!post|` are the observed memory before and after.

**Observations** (`map`, `unchanged_b`): `g:NAME` a global, `result` / `result:K`, `mK:OFF:N` or
`env:OFF:N` (N bytes of a memory), and a bit slice `OBS@HI-LO`.

### Kinds

* `equiv`: both sides start in the same symbolic state (the mapped locations agree) and run
  their calls. Goals: same trap behaviour, equal results, mapped observations equal when both
  return, the same sequence of opaque import calls (`hist`), plus the frame goals.
* `post`: one side; goals: `post` holds whenever the run returns normally, plus `no_trap` and
  `never_call` if given.
* `bmc`: like `post`, but starting from the module's initial state by default; intended for
  bounded checks of call, trap and state properties over runs.

## Verdicts

Each goal is sent to the solver as "assumptions ∧ ¬goal": `unsat` proves the goal, `sat` gives a
countermodel, anything else is unknown. The problem verdict:

| verdict | meaning |
|---|---|
| `proved` | every goal unsat, and no loop bound or inlining depth was hit (the `complete` goal is unsat), and every cut loop has a measure: all runs are covered and terminate |
| `partial` | as `proved`, but some loop was cut by an invariant without a measure: partial correctness only |
| `bounded` | every goal unsat for runs within `unroll`/`depth`; longer runs are not covered |
| `refuted` | a goal about the program (not a loop annotation) is sat and no loop was over-approximated by an invariant: the countermodel is a real run |
| `unknown` | a solver answered unknown or timed out, a loop annotation failed, or a countermodel exists only because of a cut loop or an uninterpreted spec function |
| `error` | the problem could not be loaded or executed (unsupported instruction, bad file) |

With `cases`, the verdict is `refuted` if any case is, `proved` if all are, `bounded` if all are
proved or bounded, else `unknown`. Invariants found by inference are checked like hand-written
ones; the report's `trust` field says how a verdict was obtained.

## Imports

An import is resolved, in order, by: a callee contract naming it; with `env.mem = "array"`, the
memory model below; a module of the problem with that name; otherwise it is **opaque**. Every call
of an opaque import is an event; its results are unconstrained (in `equiv`, they are a function
of the call history, so both sides receive the same answers for the same calls). A property
proved with opaque imports therefore holds for every environment.

**Memory model** (`env.mem = "array"`): one environment memory, a byte array with 64-bit
addresses, initially arbitrary or given by `env.data`:

* `mem.loadN (addr i64) -> i64`, N in 8, 16, 32, 64: little-endian load of N/8 bytes,
  zero-extended;
* `mem.storeN (addr i64, v i64)`: little-endian store of the low N/8 bytes of `v`.

**Callee contracts** (assume-guarantee). Style `values`: parameters and results are named
(`params`, `results`), `pre` is an obligation at each call, `post` is assumed of the results, and
the callee does not change Wasm state. Style `x86`: the callee runs on the x86 simulator state;
on return rsp = rsp + 8, rip = [rsp], rbx rbp r12-r15 are kept, other registers and flags are
arbitrary, memory changes only in [rsp - 0x1000, rsp), the status is 0; names `old.R` (before)
and `R` (after). Both the footprint and the "no state change" of `values` are assumptions.

## Annotated WAT problems

`wasm-vc solve f.wat` reads one exported function with SMT-LIB annotations in line comments:

```wat
;; @define (define-fun sq ((x (_ BitVec 64))) (_ BitVec 64) (bvmul x x))
;; @assume g requires P         ;; RV64: callee contract over g's parameters and `result`
;; @assume g ensures Q
;; @assume g (=> P Q)            ;; x86 split: over (old (reg r)) and (reg r)
;; @requires P
;; @ensures Q
(func $f (export "f") ...
  (loop
    ;; @invariant I              ;; for the innermost open loop (`TODO` = none)
    ;; @decreases M
    ...))
```

The flavour is recognised from the module: RV64 P-locals (`wasm-sim-rv reduce`: parameters are
the entry values of registers by ABI name, memory `env.memory`), x86 closed (`wasm-sim problems`,
`closed/`: every GPR and flag is a parameter; `(old (reg r))` is the entry value, `(reg r)` the
final simulator state, memory `env.mem` is the window at guest address 0x100000) and x86 split
(`split/<f>/`, the function runs on the shared simulator `../sim.wat` from an arbitrary state and
must return status 0). `(memN a)` reads N bits little-endian after the call, `(old (memN a))`
before. `@define (declare-fun NAME ...)` lines naming `fact`, `fib`, `gcd`, `popcount`, `tri`, `sumarr`, `sumsq` get their
standard definitions instead. A sidecar `<stem>.spec` (same or parent directory) may give
`invariant K I` and `decreases K M` lines for loop `K`. The problem is a `post` problem with
`no_trap = true` (`init = module` for RV64 and x86 closed, `symbolic` for x86 split, whose
ensures also requires status 0): requires imply that the function returns without trapping and
ensures holds.

## Trust

* `proved`, `partial`, `bounded` rely on the symbolic executor (the Wasm semantics as implemented
  in `sym/exec.rs`, the integer fragment of core Wasm: no floats, no SIMD, no `memory.grow`),
  `wasmparser` (decoding and validation) and the SMT solver. None of this is checked by Lean.
* `refuted` additionally comes with a countermodel; it is not replayed in an interpreter.
* `wasm-vc lean` produces Lean proofs that the Lean kernel checks, independently of the above. Its
  statements are partial correctness `wat_spec!` triples (`Silmaril.Wasm.WatSpec`, VC generator
  `wpc`), and its fragment is smaller: one function, no calls, no `br_table`, no conversions. The
  annotated problems themselves state total correctness (no trap, termination), so a Lean replay
  covers less than a `proved` verdict claims.
* `dag` records SMT and bounded results as evidence of status `tested`; a node is `solved` only
  with a Lean theorem.
