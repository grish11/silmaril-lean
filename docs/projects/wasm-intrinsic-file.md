# Quote a Core Wasm file as an intrinsic module

```lean
module
public import Silmaril.Wasm.Validation.Intrinsic.File

wasm_intrinsic_file witness from "module.wasm" with_raw raw with_source bytes
```

The command reads the path relative to the current Lean file. It emits an
explicit `raw : Wasm.Module`, a separate `witness : Intrinsic.Reify.Reified raw`,
and, if `with_source` is present, independent `bytes : KBytes`. Use
`witness.typed : Intrinsic.Module witness.interface` to work with the actual
context-indexed representation. The compiled Core decoder is used once in the
elaborator; it is not part of the emitted terms. The elaborator preflights
`Intrinsic.Reify.reify? raw`, but Lean independently checks its success on the
quoted **raw syntax**, not on the file or its bytes. There is no native proof or
unchecked witness. The command does not affect `wasm_module%`, `wasm_module`, or
`wasm_intrinsic`.

## Three separate claims

In another Lean file, import the file that generated the declarations as well
as `Silmaril.Wasm.Validation.Intrinsic.ReifyThms` and
`Silmaril.Wasm.Binary.Quote.Agreement`. No Wasm file is read there.

```lean
open Silmaril.Wasm.Validation Silmaril.Wasm.Binary

example : witness.typed.erase = raw := witness.erase_eq
example : ModuleOk raw witness.interface := witness.sound
wasm_prove_source agrees : bytes => raw
example : Core.decode? bytes.toByteArray = some witness.typed.erase :=
  agrees.trans (congrArg some witness.erase_eq.symm)
```

- **Exact erasure:** each successful body/function reification carries an
  equation for the original raw syntax. The module certificate preserves all
  metadata and the ordered list of erased functions. `witness.erase_eq` needs
  neither packed bytes nor a decoder theorem. `wasm_prove_erasure` still works
  for standalone typed and raw terms.
- **Intrinsic typing:** numeric operations use `numericType?_sound`; function
  and local reads use typed references. `defaultCheckers_sound` supplies the
  non-function premises, with the same environments as `validate?`.
  `witness.sound` proves the existing `ModuleOk` for the exact raw term.
- **Byte agreement:** `wasm_prove_source` separately checks the full
  `Core.decode? bytes.toByteArray = some raw` equation in the kernel. Merely
  emitting both terms does not prove this theorem.

## Coverage

Automatic reification handles straight-line numeric operations, `nop`, `drop`,
`local.get` of initialized locals, and direct calls (including imported and
recursive references). The consumed stack suffix and final result stack must
match exactly. Standard module declaration checks still apply; all raw module
metadata are retained. No automatic lifting of structured control, local
writes, stack polymorphism, subtype coercions, or the other atomic families
(e.g. memory instructions or `call_indirect`) is claimed. The explicit intrinsic
API and its propositional quotient equivalence are not restricted to this
automatic fragment.

The command reports a decoding failure as malformed input. If decoding succeeds
but reification fails, it uses the existing complete Core validator
(`validate?_isSome_iff` in `Check.ValidateFinal`) to distinguish a valid but
unsupported module from an ill-typed one. The block fixture in the regression
is a reproducible example of a valid failure to reify. There is no completeness
claim for the executable reifier. Extending it to other atomic cases requires
producing a data-level instruction signature with a checked rule (or a witness
of the actual stack adjustment); `atomC_sound` currently supplies its operand
types through a `Prop` existential. Structured control also needs indexed
branch witnesses, including the local-initialization and stack-polymorphism
invariants. Neither gap requires a second binary parser.

## Reproduce

```sh
bash tests/wasm/intrinsic-file/check.sh /tmp/wasm-intrinsic-file
```

The script verifies three pinned inputs: a defined function reading a local
and calling an import, the checked-in `sum8-closed.wasm`, and 64 generated nop
bodies. It compares raw versus raw plus intrinsic-witness construction (both
with source bytes), a fresh import, the same function-count query, and the same
`ModuleValid` proposition. It also checks source agreement after deleting the
input file, tests wrong bytes, malformed and ill-typed inputs, and audits the
emitted witness and theorems. Each Lean process has a 30 s timeout and a
4096 MiB Lean allocator limit; GNU `time` records process wall time including
imports and peak RSS. Section-indexed certificates establish byte agreement,
not stack/index typing, so they do not provide a competing operand for these
intrinsic queries.

One warm run on Linux x86-64 (seconds; raw / raw plus intrinsic witness):

| Fixture | Construct | Import | Query | Prove `ModuleValid` | Separate byte agreement |
| --- | ---: | ---: | ---: | ---: | ---: |
| Call through an import | 3.02 / 3.08 | 3.02 / 3.02 | 4.59 / 3.11 | 3.10 / 3.45 | 4.42 |
| Checked-in `sum8-closed` | 3.13 / 3.71 | 3.02 / 3.48 | 3.15 / 3.21 | 3.29 / 3.03 | 4.04 |
| 64 nop bodies | 3.01 / 3.11 | 3.06 / 3.06 | 3.05 / 3.11 | 3.15 / 3.22 | 6.73 |

Peak RSS was 2.10–2.13 GiB for construction, import, query and validity;
separate byte agreement used 2.13, 2.32 and 3.07 GiB respectively. Most wall
 time is Lean process and import cost. These are single-run measurements, not
 evidence of a speedup. The byte agreement column uses the existing
 `wasm_prove_source` proof, not the packed bounded reader.
