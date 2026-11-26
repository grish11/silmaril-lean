# PEG to ordered RVSDG and regionless MLIR

The source is the typed `PEG.Graph` with zero loop identifiers and
`Bridge.Ordered` evidence. The decidable check visits every operand occurrence
of every vertex. Each operand must name a smaller vertex number, including
both operands selected by φ and operands of vertices unreachable from the
roots. Clients with a differently numbered DAG can supply a topological
permutation to `Graph.reindex` and check the resulting table. The zero loop
frame leaves parameters, instructions and φ as the available labels.
[PEG core](../../Silmaril/SSA/PEG/Thms.lean) ·
[Bridge definitions](../../Silmaril/SSA/PEG/Bridge/RVSDG/Defs.lean)

## Translation and observation

`translate` traverses the PEG table once in vertex order and emits one
single-result RVSDG binding per vertex. A parameter emits a copy of its typed
argument slot, an instruction keeps its ordered profile, and φ emits a
value-select with operands in flag, true, false order. Operand references
become numbered output wires, so consumers of a shared vertex read its one
result. The return wires follow the PEG root tuple, including repetitions,
reorderings and empty results. The target uses the existing
`RVSDG.Term.toGraph` and `Graph.run` with value ports only.

A `TotalModel` gives each primitive a total function on defined inputs.
`TotalModel.toPEG` wraps successful primitive results in `some`. The
Figure 11 interpreter still collects **all** primitive operands strictly
before applying that function. `interpret_op_eq_none` shows that any bottom
operand forces bottom independently of the primitive interpretation.
`Ordered.demandWellFounded` proves the actual demand relation well founded
by vertex number. `observe_translate` uses the equations solved by
`Graph.denote` and compares the complete ordered root tuple to the RVSDG
tuple with `some` at every position. The proof establishes definedness at
each vertex as it extends the RVSDG local store. At φ, both arm values are
defined in the fragment, so Figure 11's lazy choice and eager value-select
return the same value. A partial primitive, effect, trap, or divergent
computation would need its own observation and evaluation-order theorem.
[Guarded Figure 11 semantics](../../Silmaril/SSA/PEG/Semantics/Thms.lean) ·
[RVSDG theorems](../../Silmaril/SSA/PEG/Bridge/RVSDG/Thms.lean)

`translateMLIR` uses the existing RVSDG–MLIR profile map and expression
translation. MLIR expressions may duplicate a shared producer. The theorem
`observe_translateMLIR` assembles the denoted MLIR result slots into the same
PEG observation. It uses the existing bridge's denotation theorem and the
fact that the induced MLIR model pulls back to the same RVSDG model.
The target is typed regionless equation syntax.
[RVSDG–MLIR bridge](rvsdg-mlir-regionless.md) ·
[PEG–MLIR theorems](../../Silmaril/SSA/PEG/Bridge/MLIR/Thms.lean)

## Satisfaction and institutional lifting

`Equation` pairs two admitted PEGs at a shared ordered boundary.
`Equation.rvsdg_satisfaction` and `Equation.mlir_satisfaction` give exact
satisfaction in the models induced from each `TotalModel`. This is the
lifting lemma for the fragment. The induced models interpret copy as
identity and select as Boolean choice. Full target signatures permit other
interpretations of those symbols.

To lift into the Peggy institution once its types are available, relate its
fixed-sort graph sentences and model satisfaction to this fragment, and pick
target model subcategories that enforce the copy/select laws and retain the
Figure 11 Bool and count carriers. A forward comorphism then needs sentence
translation and model reduct naturality under fixed-profile relabelling,
plus the satisfaction law in those target models. Consequence reflection
also needs target expansions for the source models under consideration.
The current proofs depend only on the PEG core and guarded denotation.

## Paths to other IRs

| Target | Existing entry point and remaining agreement |
| --- | --- |
| Typed λSSA | Specialize to the unary, one-result slice of `RVSDG.LambdaSSA.raiseGraph` and `GraphRelated.denote_eq`. To use it on this fragment in general, pack ordered multiple operands and roots into typed λSSA products, prove the variable/port and packing laws, and discharge the pure instruction and `TypingCoherent` premises. A future partial branch lowering needs actual γ child admission and must match the selected exit, payload, and runtime token. [Straight-line and scoped γ](rvsdg-lambdassa.md) · [Typed λSSA reverse CFG witness](rvsdg-lambdassa-acyclic-raise.md) |
| Forward flat CFG / λRTL | Introduce named typed temporaries and a return exit that carries the packed root tuple. `CFG.run_flatten` and `CFG.run_eq_toRegion` connect `LambdaRTL.Region` to the existing CFG evaluator, whose jumps dispatch only into the remaining block suffix. Prove the register allocation and lexical/store agreement with `IsSSA` or `NoClobber`. The `CFG.Version` theorems recover an SSA observation under `PairLawful` and version-zero initialization. Compare exit and payload explicitly and, for full CFG equality, account for the final store. A PEG root tuple carries no exit or final store. [λRTL and CFG contracts](ssa.md) · [Forward CFG validation](cfg-validation.md) |
| Machine RTL | Specialize the typed λSSA region to `Machine.OfLambdaSSA.RootFits` and `Compiles`, then use `ofLambdaSSA_eval_iff` with a matching call oracle and frame. Its finite outcomes are a packed word return or a trap with exact final memory. An adapter needs a word representation and ordered packing theorem, an unchanged memory argument for pure code, and a separate account of traps or absent finite outcomes where those are admitted. [Machine RTL fragment](../../Silmaril/Machine/OfLambdaSSA/Thms.lean) |

Extending PEG loops through structured RVSDG θ requires matching the initial
and feedback iteration indices, exit polarity, the first true in
the defined pass prefix, and every prefix demand of monotonized eval. Loop reversion to CFGs also
requires an explicit control-flow schedule and a return/divergence
observation. [Peggy roadmap](peggy.md) · [Ordered θ semantics](rvsdg-ordered-runtime-theta.md)

## Checks

```sh
make check CHECK_TARGETS='+Silmaril.SSA.PEG.Bridge.MLIR.Thms PEGIRBridgeTests'
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/PEGIRBridge.lean
for module in \
  Silmaril.SSA.PEG.Bridge.RVSDG.Defs Silmaril.SSA.PEG.Bridge.RVSDG.Thms \
  Silmaril.SSA.PEG.Bridge.MLIR.Defs Silmaril.SSA.PEG.Bridge.MLIR.Thms \
  Silmaril.Proofs.SSA.PEG.Bridge.RVSDG.Correctness \
  Silmaril.Proofs.SSA.PEG.Bridge.MLIR.Correctness; do
  SILMARIL_REPLAY_MODULE="$module" LEAN_NUM_THREADS=1 \
    lake env lean -DwarningAsError=true tools/compiler-explorer/Replay.lean
done
```

The fixture evaluates both φ choices in both target evaluators, compares them
to the guarded PEG observation, checks sharing and rejects a typed self-edge.
It also checks strict bottom in a primitive and an unselected bottom φ arm. [Regression](../../tests/ssa/PEGIRBridge.lean)
