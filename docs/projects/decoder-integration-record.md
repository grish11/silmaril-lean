# Decoder integration record

Provenance for the integration of the bytes → `Comp` decoder stack into `main`.

**What is integrated.** The stack's tip `e40d4fdd` (branch `components/adequacy-later-failpr`, PR #989) is brought in **by merge**, not by rebase, together with current `main`, so every source commit below keeps its SHA. On top of it come the integrator's own commits (task `5fb4bf1f`, branch `cfg/decoder-roots`).

**Status of the source PRs.** They are left **open and untouched**. This integration does not authorize closing them. Their author has not identified themself as of this record (requests on #989 and #207). The integration is non-destructive and was decided by the coordinator; it is not an assertion that the author is inactive or has approved.

**Authorship and license.** Every source commit is authored by git user `imbrem <44735514+imbrem@users.noreply.github.com>` (the shared account), and 79 of the 81 carry the trailer `Co-Authored-By: Claude Opus 5.5`. The repository is MIT-licensed (`LICENSE`, "Copyright (c) 2026 Silmaril contributors"), and the integration keeps that license and these notices unchanged.

## Source pull requests (stack order)

| PR | Branch | Base | Head | Title |
|---|---|---|---|---|
| #827 | `components/instantiation-pipeline` | `components/instantiation-starts` | `f0fbb900` | Instantiation pipeline: coreModSemI, export phase (exact), instantiation-aware acceptors, export-phase litmus, REF comparison on litmus |
| #855 | `components/component-test-shapes` | `components/instantiation-pipeline` | `287c519d` | Component tests: start functions, ordered import traces and instantiation traps on real binaries (shapes, kernel answers, REF, wasmtime oracle, explorer) |
| #921 | `components/decoder-bridge` | `components/component-test-shapes` | `4d0fc886` | Component decoder bridge: IR and REF readings of every binary agree on core instantiations |
| #930 | `components/decoder-adequacy` | `components/decoder-bridge` | `bc118dde` | Component decoder bridge: wiring, imports and exports agree in a decidable fragment; exported-instance regression |
| #935 | `components/adequacy-sim` | `components/decoder-adequacy` | `981b0418` | Component bridge: IR instantiation plays node by node; failure goal reduced to its reference half on import-wired binaries |
| #953 | `components/adequacy-ref` | `components/adequacy-sim` | `5880bd7c` | DecoderBridge.FirstCore: the reference machine traps when the IR's first core node fails |
| #967 | `components/adequacy-start` | `components/adequacy-ref` | `f1f08278` | DecoderBridge.FirstImp: first core instantiation with lowered imports and host calls |
| #979 | `components/adequacy-multi` | `components/adequacy-start` | `b6ed935d` | DecoderBridge.Multi: the start goal on several core instantiations, decomposed; IR node calls and the first node with its start epilogue proved |
| #987 | `components/adequacy-later` | `components/adequacy-multi` | `be06c145` | DecoderBridge.Multi: the instantiation on MultiImpFrag in the shared core store (Task.nodesRef proved) |
| #989 | `components/adequacy-later-failpr` | `components/adequacy-later` | `e40d4fdd` | DecoderBridge.Multi: a later failing node on MultiImpFrag traps (Task.failRefWiredRest' shrunk) |

## Source commits (81, oldest first; `git log --reverse origin/main..e40d4fdd`)

| SHA | Author date | Subject |
|---|---|---|
| `92288632d636` | 2026-11-16T10:32 | Execution-based core semantics for lowered core modules (P3) |
| `a30787c5fc7e` | 2026-11-16T18:41 | Merge remote-tracking branch 'origin/main' into components/coremod-core3-sem |
| `20b5a2da3a83` | 2026-11-16T19:23 | Component IR: instantiation phase (CoreSemI, Comp.denI), comparison with Comp.denU |
| `a8300058b953` | 2026-11-16T19:29 | InstSem: rounds and instantiation runs through the component combinators |
| `4494e8252fe6` | 2026-11-16T19:35 | InstEngine: engine semantics with an instantiation phase (engineSemI, core3SemI), instantiation runs |
| `687b70d75a22` | 2026-11-16T19:47 | InstLitmus: Core 3.0 litmus modules and components, start runs, instantiation plays (a)-(d) |
| `51788edd6b68` | 2026-11-16T19:50 | InstLitmus: scripts bounding the litmus modules at deterministic profiles |
| `0575acb42648` | 2026-11-16T19:59 | Instantiation litmus theorems (a)-(d), scripts and the protocol guard; engine export phase; caveats ledger |
| `1f95f21bfbab` | 2026-11-16T20:08 | Merge remote-tracking branch 'origin/components/coremod-core3-sem' into components/instantiation-pipeline |
| `d6810d9949b0` | 2026-11-16T20:25 | Instantiation pipeline: export phase, engine converse, coreModSemI, instantiation-aware acceptors |
| `c40b6a837d99` | 2026-11-16T20:38 | Export-phase litmus: globMod/globC/callGlobC/trap1C; extI_inst_right; trapC export phase is bottom |
| `fa78ffb1d941` | 2026-11-16T20:44 | REF comparison on litmus components: callSI/globSI/trapSI executed on the reference machine |
| `f0fbb90066ba` | 2026-11-16T20:46 | Docs: ledger, pointers from the start-free binary path to the instantiation-aware one |
| `3a3d8a58a5d2` | 2026-11-16T21:53 | Merge origin/main into components/component-test-shapes |
| `caeaa1768ef0` | 2026-11-16T22:29 | Component tests: instantiation-time behaviour of two real component binaries |
| `287c519d4f0f` | 2026-11-16T23:32 | Component tests: run REF on the decoded binaries, not a hand transcription |
| `4d0fc8868b8f` | 2026-11-17T05:17 | Component decoder bridge: the IR and REF readings of every binary agree on core instantiations |
| `bc118dde0ffb` | 2026-11-17T05:57 | Component decoder bridge: wiring, imports and exports agree in a decidable fragment |
| `388d4c3a2a7d` | 2026-11-17T06:20 | InstSem: complete rounds of composites, handlers, pairings taken apart; the routing layer of extI |
| `92a5f4e0e79a` | 2026-11-17T06:22 | InstSem: instantiation plays of import-wired components, node by node (nodesInst_of_denI) |
| `a3c2f9aa4e9b` | 2026-11-17T06:26 | InstWired: import-wired instantiation plays node by node, down to engine runs |
| `efefdd8469cd` | 2026-11-17T06:28 | DecoderBridge.Sim: the failure goal on import-wired binaries reduced to its reference half |
| `83509b77d65b` | 2026-11-17T06:29 | DecoderBridge.Sim: the instantiation part of start plays, node by node |
| `981b04186d78` | 2026-11-17T06:30 | Component tests docs and report: the IR half of the behavioural bridge on import-wired binaries |
| `144ac315668c` | 2026-11-17T07:12 | DecoderBridge.FirstCore: the fragment, the start call over any engine, the definitions before the first core instantiation |
| `7ff87073bb12` | 2026-11-17T07:15 | DecoderBridge.FirstCore: root instantiation up to the first core instantiation, over any engine |
| `5adf7edcc9a1` | 2026-11-17T07:25 | DecoderBridge.FirstCore: a trapping start function in the shared core store, and its machine run |
| `800f8a7e7b7b` | 2026-11-17T07:37 | DecoderBridge.FirstCore: a quiet failure of a node without imports, as a run of its module alone |
| `25ac87a63861` | 2026-11-17T07:42 | DecoderBridge.FirstCore: the reference machine traps when the IR's first core node fails (first-core fragment) |
| `5880bd7c4d90` | 2026-11-17T07:45 | DecoderBridge.FirstCore: headers, Task.failRefWiredRest, trap.wasm from the IR run; docs and report |
| `092e4238d7c0` | 2026-11-17T08:05 | DecoderBridge.FirstImp: the first-core fragment with lowered imports, Task.failRefWiredRest' |
| `205b98fdeace` | 2026-11-17T08:09 | DecoderBridge.FirstImp: the definitions before the first core instantiation, with their trampolines |
| `8d31b87796da` | 2026-11-17T08:10 | DecoderBridge.FirstImp: root instantiation up to the first core instantiation, with its trampolines |
| `567c5ba6590d` | 2026-11-17T08:12 | DecoderBridge.FirstImp: the first core instantiation against its trampolines |
| `eed4d1db49c2` | 2026-11-17T08:14 | DecoderBridge.FirstImp: the IR's store of imports, preparation and the start trap under renamed host code |
| `6b9090bdc7a1` | 2026-11-17T08:17 | DecoderBridge.FirstImp: the wiring of the first node of the symbolic reading |
| `fc8d048ca9ac` | 2026-11-17T08:20 | DecoderBridge.FirstImp: a quiet failure of a node with lowered imports makes no import call |
| `1575ba22c6df` | 2026-11-17T08:23 | DecoderBridge.FirstImp: the reference machine traps when the IR's first node, with lowered imports, fails |
| `9f1f226e1d7e` | 2026-11-17T08:24 | DecoderBridge.FirstImp: headers, Task.failRefWiredRest' and the relaxed first-core fragment |
| `3d104220eae8` | 2026-11-17T08:27 | DecoderBridge.FirstImp: a canon lower callout answered by answerImplS, over any engine |
| `c19e837c2f9a` | 2026-11-17T08:29 | DecoderBridge.FirstImp: callouts of trampolines of any function type |
| `b8b3befbdc53` | 2026-11-17T08:31 | DecoderBridge.FirstImp: redexes, statuses and resumption under renamed host code |
| `fa234570738c` | 2026-11-17T08:35 | DecoderBridge.FirstImp: an import call of the IR's start run, in the reference machine with the logging host |
| `78cd4dffc52c` | 2026-11-17T08:37 | DecoderBridge.FirstImp: the IR's start run with host calls, in the reference machine |
| `2c39d6498ace` | 2026-11-17T08:38 | DecoderBridge.FirstImp: the start call with the store it leaves |
| `bad4060a9786` | 2026-11-17T08:40 | DecoderBridge.FirstImp: host calls through the lowering of f, and their log |
| `90a6c8264e9e` | 2026-11-17T08:42 | DecoderBridge.FirstImp: the reference machine at the return of the first start function, with the host log |
| `5785ee0e0a87` | 2026-11-17T08:43 | DecoderBridge.FirstImp: the first node failing or ready after host calls |
| `f16166f253d4` | 2026-11-17T08:45 | DecoderBridge.FirstImp: the ready case as a run of machine steps |
| `1cc3cf331ba5` | 2026-11-17T08:46 | DecoderBridge.FirstImp: header theorems for host calls |
| `f1f08278089b` | 2026-11-17T08:47 | DecoderBridge.FirstImp: docs, caveats and report |
| `894c52419be1` | 2026-11-17T09:06 | DecoderBridge.Multi: the start goal on MultiImpFrag, decomposed into four Task props, composition proved |
| `fc3ec4f9dcfd` | 2026-11-17T09:10 | DecoderBridge.Multi: piece (a), NodeCalls of every node from the IR's node-by-node play |
| `15900d7d6449` | 2026-11-17T09:19 | DecoderBridge.Multi: root instantiation up to the first core instantiation without a trap (rootShape) |
| `a2a79c7fc31e` | 2026-11-17T09:22 | DecoderBridge.Multi: the start call with its epilogue over any engine, after host calls |
| `0b921ac6ff20` | 2026-11-17T09:32 | DecoderBridge.Multi: piece (b), the first node with its start epilogue, proved |
| `b6ed935d7491` | 2026-11-17T09:34 | DecoderBridge.Multi: docstrings, docs, caveats and report |
| `5a4c731d3560` | 2026-11-17T09:51 | DecoderBridge.Multi: relocation into a shared store with imports kept in place (GapShift) |
| `4d83a26fd6fe` | 2026-11-17T09:55 | DecoderBridge.Multi: host-free Core steps in the shared store, imports kept in place (GapStep) |
| `343f6bfe29a3` | 2026-11-17T10:00 | DecoderBridge.Multi: threads in the shared store (invocations, callouts, resumption, internal runs) |
| `87b7b9c557d9` | 2026-11-17T10:06 | DecoderBridge.Multi: RefAtDefsK (finishing continuation), pieces (b') and (c'), checked decomposition; later core modules import trampolines in order |
| `58d440edf30c` | 2026-11-17T10:09 | DecoderBridge.Multi: Task.nodesRef (the instantiation, pieces (b) and (c) together); the interface of its pieces (FirstK, LaterCoreStep, LaterInv) |
| `e2c4c8150669` | 2026-11-17T10:12 | DecoderBridge.Multi: preparation and import resolution of a later core module in the shared store (GapCore) |
| `771ebb0cd368` | 2026-11-17T10:15 | DecoderBridge.Multi: the IR's start run of a later node in the shared core store, in the machine (GapMachine) |
| `70ae1228110d` | 2026-11-17T10:17 | DecoderBridge.Multi.Later: drop the no-observation conjuncts (the instantiation's observation is the first decoding one only up to existential choice) |
| `a9b32b8ca2c6` | 2026-11-17T10:18 | DecoderBridge.Multi.Later: LaterCoreStep takes the IR node's import count |
| `e72435cc8c6c` | 2026-11-17T10:21 | DecoderBridge.Multi.LaterCore: the exports of a prepared instance, thread-table rounds, fragment facts |
| `68be07755d58` | 2026-11-17T10:17 | DecoderBridge.Multi: root instantiation with its continuation (FocusAtK, root_firstK, KFin) |
| `d3749e1f2eb7` | 2026-11-17T10:20 | DecoderBridge.Multi: the first node with a finishing continuation and the machine invariant (firstK : FirstK) |
| `0375a2e3e54a` | 2026-11-17T10:16 | DecoderBridge.Multi: aliases need distinct core export names; the symbolic reading and the frame (Nodes) |
| `80eb4964984d` | 2026-11-17T10:18 | DecoderBridge.Multi: the definitions other than core instantiations run silently (nonCore_step) |
| `b88a414eb103` | 2026-11-17T10:20 | DecoderBridge.Multi: the later definitions then the end of the instantiation (later_run) |
| `4e643ef42b5c` | 2026-11-17T10:21 | DecoderBridge.Multi: Task.nodesRef from FirstK' and LaterCoreStep' (nodesRef_of') |
| `8951aa1b7d73` | 2026-11-17T10:24 | WIP LaterCore: later core instantiation, no-start case (start case pending) |
| `c4ba4b839246` | 2026-11-17T10:28 | DecoderBridge.Multi.LaterCore: a later core instantiation in the shared core store (laterCoreStep' : LaterCoreStep') |
| `2077a1a99cba` | 2026-11-17T10:45 | DecoderBridge.Multi: the instantiation on MultiImpFrag proved (Task.nodesRef); the start goal on the fragment reduced to the export call (startAdequacyFrag_of_d, starts_of_d); docs and report |
| `be06c14500bd` | 2026-11-17T10:46 | DecoderBridge: docstrings after Task.nodesRef |
| `f03c4f794185` | 2026-11-17T10:37 | DecoderBridge.Multi: a later core instantiation that fails quietly traps (laterFailStep); quiet ready nodes make no call |
| `76a0c2ef1884` | 2026-11-17T10:40 | DecoderBridge.Multi: a later node fails in the fragment, the reference instantiation traps (laterFail_ref); Task.failRefWiredRest'' and failRefWiredRest'_of_rest''_of_firstK' |
| `080cdf2ce821` | 2026-11-17T10:55 | DecoderBridge.Multi.Thms: failRefWiredRest'_of_rest'' unconditional (firstK'); docs |
| `e40d4fdd5256` | 2026-11-17T10:55 | docs: the later failing node on MultiImpFrag |
