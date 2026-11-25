# Intrinsic typing of the SQLite reactor initializer

`SqliteWasm.typedInitializer` is a Core `Validation.Intrinsic.Function`
for `_initialize` at function index 25, defined ordinal 2. The term uses
the context prepared by the ordinary Core validator from the pinned
reactor. Its signature is the one at that ordinal. The stack indices
check the guard block and conditional branch, the address calculation,
the memory load and store, and both calls in order. The function indices
resolve against the full context, including the 23 imports.

`originalIntrinsicInitializer` equates the erased function with the
function selected by the ordinary decoder on the original byte literal.
`originalInitializerTyped` derives `FuncOk` in the prepared context.
Together these cover the function's type index, locals, and entire
instruction tree. The scope is this single function. The startup
reduction and whole-module validity are separate judgments.
[Original decode](../whole-module/README.md) · [Context preparation](../validation/ValidationInputs.lean)

## Reproduce

Run the [whole-module check](../whole-module/README.md#reproduce) before
building the intrinsic fixture with the same generated Lean directory.

```sh
bash tools/sqlite-wasm/intrinsic-export/check.sh .lake/sqlite-wasm/lean/SqliteWasm
```

The script checks erasure, an ordinary downstream import, and the
theorems' inherited axioms.
