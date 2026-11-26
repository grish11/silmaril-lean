# Scalar MLIR Math and Complex

The profile admits flag-free scalar `f64` and `complex<f64>` operations with
already typed operands. Exact Math values use Mathlib's `ℝ`, and exact Complex
values use `ℂ`. The evaluators use 64-bit encodings for Math and ordered pairs
of encodings for Complex. The real component comes first.
[Math definitions](../../Silmaril/SSA/MLIR/Math/Defs.lean) ·
[Complex definitions](../../Silmaril/SSA/MLIR/Complex/Defs.lean)

## Denotation and policies

`MathCollection.Collection` interprets a typed family of operation symbols.
Each operation supplies a `Reference` with a domain and a value function that
requires a proof of domain membership. It can also supply a local
`executable`, a function on the encoded carriers. Both dialects expose
computable `Op.executable` dispatch independently of their exact denotations.
[Collection contract](../../Silmaril/SSA/MLIR/Math/Collection/Defs.lean)

`Operation.RealizesOn` concerns a backend result relation on a stated set of
encoded inputs. It requires a related result for every admitted input and
checks every related result. Acceptance requires the input to decode, the
decoded input to satisfy the reference domain, and the encoded output to pass
the chosen `Observation`. The output policy can inspect the input encoding,
including bits lost by decoding. The contract is parametric in that policy.
A result relation reporting only successful returns needs separate evidence
about traps or other terminal outcomes.

All local evaluators are bit operations with no rounding. The `absf` model
clears the sign bit, and conjugation toggles the imaginary sign bit. The
construction and projections transport encodings unchanged, including signed
zeros, infinities and NaN payloads. `Observation.exact` compares decoded
results and therefore observes only distinctions the decoder retains.
`create_realizes` uses that policy on the domain where both components decode.
The separate bit laws for projections and conjugation quantify over every
binary64 encoding. [Binary64 definitions](../../Silmaril/SSA/MLIR/Math/Binary64/Defs.lean) ·
[Complex theorems](../../Silmaril/SSA/MLIR/Complex/Thms.lean)

The `log` reference has domain `0 < x`. `log_one` gives the reference result
at one, and `log_rejects_decoded_zero` excludes any result at a decoded zero for
every output policy. Its local evaluator is absent. The exact reference for
`absf` is real absolute value on all reals. Its idempotence and the encoded
idempotence are checked independently. [Math theorems](../../Silmaril/SSA/MLIR/Math/Thms.lean)

This milestone covers operation denotations and local laws. MLIR parsing,
attribute verification, `fastmath`, vector and tensor lifting, other floating
formats, target behavior and integration with the SSA graph are outside the
profile. Its NaN and signed-zero bit examples describe the local evaluator.

## Libm and WebAssembly adapter

`Silmaril.Wasm.SSA.MLIRMath` combines the SSA contract with Numeric.Libm using
Wasm's existing region dependencies. `ofF64_toF64` and `toF64_ofF64` prove
both bit reinterpretation round trips. `absf_fabs_bits` and `conj_neg_bits`
identify the scalar bit operations with `Double.Ref.fabs` and `F64.neg` on
every encoding. `complex_create_realizes` instantiates the exact component
observation with the finite rational decoder `F64.toRat?` followed by the
cast to `ℝ`. [Region map](../../regions.toml) ·
[Adapter definitions](../../Silmaril/Wasm/SSA/MLIRMath/Defs.lean) ·
[Adapter theorems](../../Silmaril/Wasm/SSA/MLIRMath/Thms.lean)

`log_exact_iff` identifies the exact result graph of `Double.log` with the
MLIR reference on decoded inputs. `log_one_exact` checks that result on the
binary64 encoding of one. `log_in_catalogue` checks membership, and
`log_node_of_catalogue` derives the MLIR rounding observation from a
`Double.ValidLibmDouble .correctlyRounded` hypothesis. `log_exports_of_valid`
transfers the corresponding Wasm value contract to `LogNode`, using
`LibmFloat.CR` for nearest ties to even. These implications require rounding
evidence for the candidate. Signed zeros and nonfinite encodings fall outside
the admitted logarithm domain. Libm flags and `errno`, and complex arithmetic
accuracy, are outside the adapter's value observation.
[Libm catalogue](../../Silmaril/Numeric/Libm/Catalogue/Defs.lean) ·
[Elementary specs](../../Silmaril/Numeric/Libm/Elementary/Defs.lean) ·
[Wasm exports](../../Silmaril/Numeric/Libm/Wasm/Defs.lean)

`absf_build_exports` lifts the existing unary instruction checker to equality
with the MLIR bit model. `fabs_fixture_checked` kernel-checks a 39-byte
original module exporting `local.get 0; f64.abs`. `fabs_fixture_exports`
applies the bridge at every deterministic Wasm numerics profile. The checked
property is bit equality with the MLIR evaluator, including signed zeros and
NaN encodings. The adapter and its hand-encoded fixture are original Silmaril
contributions under the repository's MIT license. The fixture uses encodings
from the pinned WebAssembly specification. Its SHA-256 is
`a9ce443286440e88df3d6e8df25a1592e55010e7320418f2e57473cf49436185`.
[Fixture](../../Silmaril/Wasm/SSA/MLIRMath/Examples/Thms.lean) ·
[Wasm pin](../../specs/wasm/core-3.0.json) · [Silmaril license](../../LICENSE)

## Upstream inventory

The inventories below enumerate the operations in `MathOps.td` and
`ComplexOps.td` at LLVM commit
`cc45e189bc99870d26d50c5e3a3d215068e74880`. Each checked entry refers only to
the scalar profile above. [Pinned Math TableGen](https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/mlir/include/mlir/Dialect/Math/IR/MathOps.td) ·
[Pinned Complex TableGen](https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/mlir/include/mlir/Dialect/Complex/IR/ComplexOps.td)

| Math status | Operations | Scope |
| --- | --- | --- |
| Checked reference and executable | `math.absf` | Real absolute value and binary64 sign clearing. |
| Checked reference | `math.log` | Positive reals. A backend guarantee requires an output policy and evidence. |
| Planned | `math.absi`, `math.ctlz`, `math.ctpop`, `math.cttz`, `math.ipowi` | Require integer width, index and exceptional-input profiles. |
| Planned | `math.isfinite`, `math.isinf`, `math.isnan`, `math.isnormal` | Require a floating classification profile and boolean results. |
| Planned | `math.copysign`, `math.ceil`, `math.floor`, `math.round`, `math.roundeven`, `math.trunc`, `math.clampf`, `math.fma`, `math.sqrt` | Require per-operation bit or rounding semantics, including FMA's rounding attribute. |
| Planned | `math.acos`, `math.acosh`, `math.asin`, `math.asinh`, `math.atan`, `math.atan2`, `math.atanh`, `math.cbrt`, `math.cos`, `math.cosh`, `math.erf`, `math.erfc`, `math.exp`, `math.exp2`, `math.expm1`, `math.fpowi`, `math.log10`, `math.log1p`, `math.log2`, `math.powf`, `math.rsqrt`, `math.sin`, `math.sincos`, `math.sinh`, `math.tan`, `math.tanh` | Require operation-specific domains and policies, including paired results for `sincos`. |

| Complex status | Operations | Scope |
| --- | --- | --- |
| Checked reference and executable | `complex.create`, `complex.re`, `complex.im`, `complex.conj` | Mathematical construction, projections and conjugation, with the corresponding binary64 component model. |
| Planned | `complex.bitcast`, `complex.constant` | Require representation and attribute decoding contracts. |
| Planned | `complex.eq`, `complex.neq` | Require floating comparison semantics. |
| Planned | `complex.add`, `complex.sub`, `complex.mul`, `complex.div`, `complex.neg` | Require arithmetic or sign profiles and their special-value rules. |
| Planned | `complex.abs`, `complex.angle`, `complex.atan2`, `complex.cos`, `complex.exp`, `complex.expm1`, `complex.log`, `complex.log1p`, `complex.pow`, `complex.powi`, `complex.rsqrt`, `complex.sign`, `complex.sin`, `complex.sqrt`, `complex.tan`, `complex.tanh` | Require domains and applicable branch conventions or numerical policies. |

The public generated documentation was consulted alongside TableGen. The
pinned Complex-to-Standard lowering documents the choice of a separate
imaginary negation and reconstruction for conjugation. All Lean code here is
original, using Lean bitvectors and Mathlib. The LLVM references are under
Apache-2.0 with the LLVM exception. [Math docs](https://mlir.llvm.org/docs/Dialects/MathOps/) ·
[Complex docs](https://mlir.llvm.org/docs/Dialects/ComplexOps/) ·
[Pinned conjugation lowering](https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/mlir/lib/Conversion/ComplexToStandard/ComplexToStandard.cpp) ·
[LLVM license](https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/llvm/LICENSE.TXT)

## Checks

```sh
scripts/check-layout.sh
lake build --wfail +Silmaril.SSA.MLIR.Math.Thms +Silmaril.SSA.MLIR.Complex.Thms
make check CHECK_TARGETS='+Silmaril.SSA.MLIR.Math.Thms +Silmaril.SSA.MLIR.Complex.Thms'
lake build --wfail +Silmaril.Wasm.SSA.MLIRMath.Examples.Thms
make check CHECK_TARGETS='+Silmaril.Wasm.SSA.MLIRMath.Examples.Thms'
```
