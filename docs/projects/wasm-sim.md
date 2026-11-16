# Simulators in Wasm: the Lean framework (region `Sim`)

**Emulators compiled to Wasm, not semantics of Wasm.** The programs on this page are x86-64
simulators *written in* WebAssembly; the Wasm semantics they run on is the Core 3.0 model of
[wasm-semantics.md](wasm-semantics.md). For interpreters and semantics *of* Wasm, see the
[Wasm catalogue](wasm-catalog.md).

An ISA simulator written in WebAssembly turns problems about an ISA (here x86-64) into
problems about a Wasm module: if the simulator is **sound** for the ISA, a property proved of
the simulator running a program is a property of the program on the ISA. This page describes
the Lean side: one simulator interface, one reduction record, and the transfer theorems that
connect them. The ABI of the simulators (locations, imports, exports, status codes) is in
[wasm-sim-abi.md](wasm-sim-abi.md); the problem-level pipeline (DAGs of small Wasm problems) is in
[wasm-sim-reduction.md](wasm-sim-reduction.md). Everything listed as proved is proved with the standard axioms.

## The canonical stack

```
Machine / Simulation        Silmaril.Sim.Core        simulator and ISA are both Machines; soundness
        │                                         is a Simulation of the simulator by the ISA
ExportSim.Cert              Silmaril.Sim.Wasm        a Core 3 module, one export per command; a
        │  Cert.simulation                        certificate gives Simulation K.toMachine B
Decomp                      Silmaril.Sim.Reduce.Core one goal, many pieces, a composition theorem
        │
transfer                    Simulation.{sem, angelic, reaches}, Institution.transfer,
                            isaReach_of_wasmTotal, specReduction (x86 System V)
```

1. **`Silmaril.Sim.Core`.** `Machine C L V` (`St`, `view : St → PState L V`, `step`), built from a
   deterministic ISA by `Machine.ofStep`; programs `Prog C L V`; properties `HAngelic` (some
   run: the `FnContract.Spec.Total` shape), `HDemonic` (every run: the `FSpecValid` shape),
   `Must` (demonic total correctness). Soundness is `Simulation A B` (view below the
   reference, steps matched, every reference state loadable; `FwdSim` is the step part);
   completeness is `CoSimulation`; `Equiv` is both with equal views (representation
   equivalence). Transfer: `Simulation.sem`, `Simulation.angelic`, `Simulation.reaches` (the
   `Reaches` form for `Machine.ofStep`), `Simulation.trans`, `CoSimulation.demonic`,
   `CoSimulation.must`; `Simulation.ofMethods` builds a simulation from per-command triples.
2. **`Silmaril.Sim.Wasm`.** `ExportSim C L V H`: a profile, a host relation (the opaque imports),
   the view `get` of a store, and per command an export address, its arguments and the
   accepted results. `ExportSim.call` (`$invoke` of the export returns accepted results) is the
   one call relation; `ExportSim.toMachine` is the simulator as a `Machine`. `MethodOK K B R c`
   is the per-method soundness problem; `ExportSim.Cert K B` (relation, view, loading,
   `MethodOK` for every command) gives `Cert.simulation : Simulation K.toMachine B`. The header
   imports only `Silmaril.Sim.Core` and `Silmaril.Wasm.Logic.Hoare`. `MethodOK` follows from
   * `methodOK_of_fspecValid`, `methodOK_of_fspecValidU`: every-run triples (`Hoare.FSpecValid`);
   * `methodOK_of_ctxSat`, `reductionCore`: a core valid relative to accessor contracts
     (`Hoare.CtxSat`), accessors that are functions of the same module;
   * `Silmaril.Sim.Wasm.FnSpec`: `methodOK_of_vc` (a `wasm_vc` proof of `methodFnSpec`);
   * `Silmaril.Sim.Wasm.Open`: `methodOK_of_moduleSat` (an open module under the most general
     environment of its import contracts) and `methodOK_of_core` (a core verified once as an
     open module, accessors supplied per representation).
3. **`Silmaril.Sim.Reduce.Core`.** `Decomp {goal, pieces, compose}` is the reduction record;
   `Decomp.Exact` (pieces follow from the goal) gives refutation transfer; `Decomp.single` is a
   one-piece reduction; `Decomp.refine` replaces a piece by its own decomposition; `agDecomp`
   (assume-guarantee over an acyclic call graph) and `cut_compose` (cut points) are the
   decomposition combinators. `Silmaril.Sim.Institution.Reduction goal` is the same data indexed
   by its goal (`Decomp.ofReduction`, `Decomp.toReduction`, round trips by `rfl`), so the
   institution's combinators (`Reduction.transfer`, `link`, `perCmd`, `wasmMethods`, `chain`,
   `equiv`, `accessors`, `ExportSim.reduction`) produce `Decomp`s.
4. **Transfer.** At the run level, `SoundSim σ W` is the projection of a sound simulator that the
   problem statements use; `SoundSim.ofSimulation` and `SoundSim.ofExportCert` build it.
   `isaReach_of_wasmTotal` (a Wasm solution solves `IsaReach step Pre Post`, given `Encodes`)
   is the run-level form of `Simulation.reaches`; `wasmTotal_of_isaReach`, `isaCex_of_wasmCex`
   need run-level completeness (`RunComplete`). For x86-64 System V contracts,
   `Silmaril.Sim.Reduce.X86`: `spec_total_iff`, `specReduction`, `specExact`. Across signatures:
   `Institution.transfer` (sound simulators, upward-closed angelic sentences),
   `transfer_demonic` (complete simulators), `transfer_exact` (exact simulators), `link`
   (callees as opaque commands).

## Instances

| instance | module | simulator | reference machine | status |
|---|---|---|---|---|
| x86 G certificate | `Silmaril.Sim.X86.GCert` (`cert`, `sound`) | `exportSim`: the certified G step methods (`Silmaril.Sim.X86.G.emit`) as an `ExportSim` | `xRef`: `Silmaril.X86.Ext.exec`, undefined flags concretized | proved |
| x86 G institution | `Silmaril.Sim.X86.GInst` (`coSim`, `reduce_inst`) | `wasmM`: stores stepping by the Wasm runs of `emit c` | `x86M` (= `xRef`) | proved (`CoSimulation`, demonic transfer) |
| x86 System V wrapper | `Silmaril.Sim.SysV` (`reduce`, `wrapper_sound`, `xgoal_of_body`) | the G simulator called through the System V descriptor | `FnContract.Spec.Total` on `Open9.isa` | proved for the G fragment |
| *(not in this repository yet)* RV64 memory-state simulator | `Sim.RV64.Reduce` (`reduce`) | `simM`, export `step`, state in memory | `Silmaril.RiscV` `decode`/`step` | proved by its own triple chain; an `ExportSim.Cert` instance is pending |
| *(not in this repository yet)* WASI trace layer | `Sim.WasiBridge` | syscall ↔ WASI adapters | Linux process events | definitions and trace lemmas; not yet a `Cert` |

## Proved vs tested

| artefact | status |
|---|---|
| the G translator: `emit`/`emitX`/`emitProg` (x86-64 register fragment → Wasm methods), `emit_sound`, `GCert.cert` | **proved** |
| P-calls and dispatcher routes (`Silmaril.Sim.Reduce.PCalls`, `Silmaril.Sim.Reduce.Loop`); the toy's `dbl`, `sum_to` and `f` end to end (`Silmaril.Sim.Reduce.Toy`) | **proved** |
| the G simulator with a guest memory window (`Silmaril.Sim.X86.GM`: `MemEnc.load`/`store`, `emitM_sound`) and the monolithic toy (`Silmaril.Sim.X86.Toy`) | **proved** |
| `Silmaril.Sim.Example`: a three-location toy ISA and a partial simulator, a non-vacuity check of the framework | **proved** |
| real ELF functions through the reduction (`Silmaril.Sim.ElfVerify`): `bswap32_manual` and `sat_add_u32` of the pinned `examples/elf-ladder/01-leaf-arith` executable meet the ladder's own specifications on `Open9.isa` (`bswapSpec_total_open9`, `SatAdd.satSpec_total_open9`) | **proved** |
| the transfer principles and the toy's pieces as catalogue problems (`Silmaril.Problems.WasmSim`, `@[problem]` IDs `wasm-sim/…`) | **proved** (`@[solves]`) |
| the run-time simulators `examples/wasm-sim/x86/x86-g.wat`, `x86-m.wat` | **tested only** (difftests against native execution) |
| `wasm-sim reduce` (ELF reader, decoder, translator) | untrusted tooling; its outputs are checked or restated in Lean |

The proved x86 artefact is a certified **translator** from a register fragment to Wasm methods,
not the run-time `x86-g.wat`.

## Derived and deleted forms

* `Silmaril.Sim.WasmSim` (store machine) and `WasmSim.Obligations`: derived. A `WasmSim` is a
  `Machine` (`WasmSim.toMachine`); `ExportSim.toWasmSim` and `Cert.obligations` are kept for
  existing statements; new code uses `ExportSim.toMachine` and `Cert.simulation`.
* `Silmaril.Sim.Reduce.Wasm.CoreSim` and `CallReturns`: deleted (no instance). `runSpec`,
  `wasmTotal_of_runSpec` and `specRunReduction` are stated over an `ExportSim` certificate.
* `Silmaril.Sim.Reduce.Reduction` (`src`, `tgt`, `sound`): legacy two-field form, kept for existing
  statements; `Reduction.toDecomp` converts; `Reduction.trans` is deprecated (use
  `Decomp.refine`).
* `Silmaril.Sim.Institution.Reduction`: the goal-indexed view of `Decomp`.
* `Decomp.ofCore`, `Decomp.toCore`: deprecated aliases of `Decomp.ofReduction`,
  `Decomp.toReduction`. The modules `Silmaril.Sim.Reduce.Bridge` and `Silmaril.Sim.Reduce.Interop`
  were folded into `Silmaril.Sim.Reduce.Core`.

## Representations and undefined values

* **G ≡ M** (`Sound.of_repr`, `Equiv.reduct`, `Reduction.accessors`): each representation is a
  machine over accessor commands, the shared core a substitution; an `Equiv` of the accessor
  machines lifts to the simulators. At the Wasm level: `methodOK_of_core` (open module) and
  `methodOK_of_ctxSat` (same-module accessors).
* **Specialised code** (`FwdSim.block_transfer`, `FwdSim.prog_transfer`): registers as locals,
  methods inlined, with control flow through `Prog.cfg` and the cut-point rules
  `HAngelic.cfg_of_measure`, `HDemonic.cfg`.
* **Undefined values**: a simulator that draws undefined values from `nd.undef` is *exact*
  (`PSim.SoundExact`), so `Simulation.angelicExact` and `Institution.transfer_exact` transfer
  properties whose guards branch on them. Otherwise translated guards must be upward closed
  (`Sig.Hom.mono`); a branch on an undefined flag is then not taken, which is sound but can
  lose progress.

## Not covered

* `Problems.FnCorrect` over a whole model class: only the single-machine `Machine.Must` is
  bridged (`Silmaril.Sim.Machine`).
* For a concrete module: that `get` agrees with the module's `get` export, and that
  `instantiateOnce?` produces stores in the certificate's relation, are per-simulator facts
  (proved for the G module in `Silmaril.Sim.X86.GCert`).
* The run-time simulators are not proved (see the table above). `Silmaril.Sim.X86Real` quotes
  both of them verbatim (`simG`, `simM`; `wasm-sim lean-quote --check` keeps the quotation equal
  to the files) and proves a first slice of the shipped G code: the accessors
  (`rgetG_total`, …, `fset6G_total`), `core_of_accessors` and the ALU method `i_alu_rr` for
  add/sub/cmp at width 8 (`iAluRR_G`, `aluFlags_add`, `aluFlags_sub`). An `ExportSim.Cert` for
  the whole shipped module is open.

## Reproduce and test

The run-time simulators are generated from `examples/wasm-sim/x86/src/*.wat`. The Rust
harness (`tools/wasm-sim`: wasmtime 50, iced-x86) regenerates and tests them. It is untrusted
tooling: no Lean statement depends on its output, except that `max2.wat` and the two simulators
are quoted verbatim in Lean.

```sh
(cd tools/wasm-sim && cargo build --release --locked)      # Rust 1.98.1 (rust-toolchain.toml)
W=tools/wasm-sim/target/release/wasm-sim
$W gen-x86                       # regenerate x86-{g,m}.wat; the committed files are its output
$W lean-quote --check            # Silmaril/Sim/X86Real/Defs.lean quotes them verbatim
$W difftest-insn --sim g         # single instructions against the host CPU (also --sim m)
$W difftest-fn --sim g [--c]     # whole functions of tests/funcs.S (or gcc -O2 tests/cfuncs.c)
$W problems -o /tmp/problems     # the problem modules of examples/wasm-sim/x86/problems
lake build Silmaril.Sim.X86.GCert.Thms Silmaril.Sim.X86Real.Thms
```

On an x86-64 Linux host (gcc 14.2.0, GNU as 2.44), `difftest-insn` passed 20,400 of 20,400
cases for each of G and M, and `difftest-fn` passed every function (14 assembly and 17 C
functions, 300 random inputs each) with 0 failures. The problem modules of the assembly
functions regenerate byte for byte. The six from `cfuncs.c` depend on the C compiler version,
so another gcc may regenerate different code; `problems --check` additionally needs `z3`.
These are tests, not proofs.
