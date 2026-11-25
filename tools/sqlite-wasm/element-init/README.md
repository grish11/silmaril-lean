# SQLite reactor element initializer expressions

The original decoded reactor has one element initializer vector of 342
singleton `ref.func` expressions. The kernel checks the exact order
against the quoted expressions and checks each index against the 1,556
function slots. [Original decoder theorem](../whole-module/README.md) · [Artifact pin](../reactor.json)

`reactorElementReplay` proves that ordinary Core `evalExprss? evalConst?`
returns that vector's function references in order, with the incoming
store and frame unchanged. Its premise identifies the frame's function
address vector as `List.range 1556`. The proof derives each lookup by
the range law and composes the existing evaluator equations by induction.

`reactorProvisionalElementReplay` uses the 23 typed function imports
with canonical addresses. The ordinary global and table evaluators
produce the provisional frame, whose function addresses meet that
premise. The theorem covers evaluation of the reference expressions.
Applying the references to the table is a separate stage.

After the [original decoder check](../whole-module/README.md#reproduce), run

```sh
bash tools/sqlite-wasm/element-init/check.sh .lake/sqlite-wasm/lean/SqliteWasm
```

The downstream module imports `SqliteWasm.ElementInit` from the generated
Lean root, checks the original decoder connection and audits the three
public theorems. [Statements](ElementInit.lean) · [Downstream check](ImportCheck.lean)
