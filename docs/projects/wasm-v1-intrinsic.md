# Native intrinsic Wasm 1.0 scalar fragment

Use `Silmaril.Wasm.V1.Intrinsic.Scalar.Thms`. `Instr` carries a native V1
context and exact input and output stacks. Local reads and writes resolve the
native local index; a direct call consumes the resolved parameters and pushes
the results. `Body.step` frames a preserved stack prefix and composes the
remaining effect with the rest of the body. The constructors are data and there
is no escape hatch for arbitrary source instructions.

`Function` adds the native type-index lookup, zero-initialized local declarations,
and an empty-to-results body; V1 permits at most one result. `ClosedModule` puts
one type and one function in scope before constructing the body and exports that
function. Self calls are expressible without infinite syntax; typing does not
imply termination. This shape has no other sections. The instruction slice is
integer constants/arithmetic/comparisons, scalar `select`, locals and direct
calls. It does not model structured control, unreachable-stack polymorphism,
floating-point operations, memory, tables or host imports.

`Instr.sound` and `Body.sound` derive V1's actual declarative judgments.
`Function.sound` and `ClosedModule.sound` inhabit the Wasm1 profile judgments.
`ClosedModule.toCore_eq` says direct emission equals the existing V1→Core
translation of the native erasure, including the function locals, signature,
body and export. `ClosedModule.core_sound` then uses existing validation
preservation. `ClosedModule.ofCore?_toCore` recovers the **raw V1 AST**, not an
intrinsic witness. `ClosedModule.lime_sound` and `ClosedModule.lime_toCore_eq`
give an additional exact route through the native Lime AST and judgment using
the existing V1 embedding. No `HasIntrinsic Wasm1` or Lime instance is provided:
arbitrary checked source can have a different shape or unsupported instructions.
This is not a reifier, binary roundtrip, execution proof or new V2 typed family.

Reproduce the typing, erasure, negative elaboration and axiom checks:

```sh
make check CHECK_TARGETS=+Silmaril.Wasm.V1.Intrinsic.Scalar.Thms
```
