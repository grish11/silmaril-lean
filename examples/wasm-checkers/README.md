# Verified checkers as Wasm binaries

| File | Bytes | SHA-256 | Lean module (the proof target) | Main theorems |
| --- | --- | --- | --- | --- |
| `lrat.wasm` | 1812 | `2a7e04b514053262880547d1baf5d92fdfabddef6a4af2fce8bb7f1a08e1f2fc` | `Silmaril.Wasm.Examples.LRAT.lratModule` | `lrat_session_unsat`, `lrat_spec`, `unitPair_accepted` (`Silmaril.Wasm.Examples.LRAT.Thms`) |
| `farkas.wasm` | 372 | `795802670fece3cde2e876f4c1bf0446bdb704988c2d4e07b7a2e83143a45ab0` | `Silmaril.Wasm.Examples.Farkas.farkasMod` | `farkas_session`, `farkas_session_infeasible` (`Silmaril.Wasm.Examples.Farkas.Thms`) |

**What ties a file to its theorems.** The theorems are about a Lean `Module` value under the Core
3.0 semantics, at every numeric profile and environment. `Silmaril.Wasm.Examples.{LRAT,Farkas}.Bytes.Thms`
prove, by kernel evaluation, that silmaril's encoder writes exactly `bytes` for that module
(`encodeModule_eq`), that `bytes` encodes it in the specification's binary grammar
(`bytes_encodes`) and that the decoder reads it back (`decode_bytes`).
`scripts/check-wasm-checkers.py` (run by `make check`) checks that each file here is exactly
that `bytes` literal. Both files are registered in `silmaril/artifacts.toml` and appear in the
explorer's Wasm pages, merged with the Lean module by SHA-256.

**What is not proved.** That a particular engine (V8, wasmtime, …) implements Core 3.0 on these
bytes. `test-lrat.mjs` runs `lrat.wasm` on Node with the sessions of
`Silmaril.Proofs.Wasm.Examples.LRAT.Tests` (four accepted refutations, including RAT steps, and
six rejected inputs); it is a test, not a proof.

```sh
python3 -I scripts/check-wasm-checkers.py
node examples/wasm-checkers/test-lrat.mjs
lake build --wfail Silmaril.Wasm.Examples.LRAT.Bytes.Thms Silmaril.Wasm.Examples.Farkas.Bytes.Thms
```

To regenerate a file, write `Binaryen.Exe.encodeModule? lratModule` (or `farkasMod`) to disk;
the build fails if it no longer equals `bytes`.
