# Explicit Wasm module terms

The quotation commands use the compiled Core decoder as an elaboration-time
constructor. The generated `Wasm.Module` uses explicit syntax constructors;
embedded `ByteArray` payloads use packed literals. Neither constructing nor
importing the resulting term runs Wasm validation or proves source agreement.

```lean
module
public import Silmaril.Wasm.Binary.Quote.Defs

wasm_module exampleModule from "example.wasm" with_source exampleBytes
```

The path is relative to the current Lean file. Omit `with_source exampleBytes`
to emit only the module, or use `wasm_module% "example.wasm"` in term position.
The command publishes the definitions so an importing module can reduce field
projections. Malformed binaries rejected by the Core reader are rejected at
elaboration; a syntactically decodable but ill-typed module can still be quoted.
There is no file lookup during import.

To prove the exact source equation separately, including from another module:

```lean
module
public import YourModule
public import Silmaril.Wasm.Binary.Quote.Agreement

wasm_prove_source exampleAgreement : exampleBytes => exampleModule
```

The theorem states `Core.decode? exampleBytes.toByteArray = some exampleModule`.
The command submits a reflexivity proof of the proved-equivalent `decodeF`
equation to Lean's kernel. There is no native proof fallback or guarantee that
large examples finish within the kernel budget. The theorem relates two Lean
values; it does not attest to a path, file provenance, later file contents,
typing, or equivalence to an intrinsic representation.

Run `bash tests/wasm/quote/check.sh` for construction and import, source mismatch,
malformed input, an ill-typed input that still decodes, and the agreement axiom
audit. The fixtures are a checked-in small Wasm binary and explicit byte strings
in the test script; no large binaries are needed.
