# Core serialization: one passive data segment

`PassiveSerialize` stages one format profile for both actual `ModuleOk` and
the existing context-indexed `Validation.Intrinsic.Module`. Its only metadata
is one passive segment in an otherwise empty module with empty interface.
There are no function or memory indices, code bodies, local groups, names,
imports, exports, active segments, or additional data vectors here. It does
not assert that arbitrary valid modules fit the encoder or decoder profiles.

`Fits` checks the payload vector length and full data section body separately,
each strictly below `2^32`. Section body bytes are the one-byte count and mode,
minimal unsigned LEB128 payload length, and the payload. Thus `2^32 − 8`
payload bytes fit and `2^32 − 7` do not, even though the latter length fits
`u32` on its own. The regression tests these bounds arithmetically without
allocating multi-GiB arrays. There is no resource-usage guarantee at these sizes.

`decode_encode` proves actual `Core.decode?` success for **all** payloads
with those bounds. It proves the real Core reader reads each encoded LEB
(all five widths) and consumes the section through EOF; the passive packed
certificate uses the same final decode assembly. The proof is symbolic,
not a finite test or an assumption of successful decode. Both raw and
intrinsic serializable subtypes get exact raw AST roundtrips. The latter's
typed recovery is equality in `Intrinsic.Module.Erasure`, not equality of
proof-relevant witnesses. The input recognizer runs ordinary `Core.decode?`
and then checks AST shape and size; `decodePayload_sound` links success to
the exact decoder result. This is an AST roundtrip, **not** a byte-level
inverse for arbitrary accepted inputs: encoding emits minimal LEBs and
omits custom and data-count sections. It is not a claim about Binaryen's
encoder or about execution equivalence of arbitrary modules.

```sh
lake build --wfail +Silmaril.Wasm.Binary.Core.PassiveSerialize.Thms
lake env lean -j1 -M4096 -DautoImplicit=false -E warning tests/wasm/passive-serialize/Regression.lean
lake env lean -j1 -M4096 -DautoImplicit=false -E warning benchmarks/wasm-kernel-decode/PassiveRegression.lean
```
