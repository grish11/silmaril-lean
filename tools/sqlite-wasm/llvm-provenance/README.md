# Retained LLVM stages of the pinned SQLite reactor

The ordinary WASI build can retain its early LLVM bitcode and relocatable Wasm
object while linking the same pinned reactor bytes. The driver trace records
Clang 21.1.4, its preprocessing, bitcode, backend, assembler and linker
commands, and the linker and symbol tool versions. Only the temporary build
root in the trace is replaced with `<build>`. Clang emits the retained
bitcode with `-disable-llvm-passes`, then feeds it to the `-Os` backend.
[Build](../build.sh) · [Exact driver trace](clang-stages.txt) · [Receipt](receipt.json)

| Stage | Bytes |
| --- | ---: |
| Early LLVM bitcode | 2,767,256 |
| Relocatable Wasm object | 958,931 |
| Linked reactor | 741,717 |

The receipt checks every framed Code offset and length against the linker map.
For each of five selected symbols it requires one defined entry from `llvm-nm`
in both intermediates and one Code frame linked from `sqlite3.o`. The size of
the relocatable symbol must equal the linked frame size. The frame determines
its import-first Wasm slot, and the getter is also checked against the export
section. Code spans include the size LEB. The linked reactor's SHA-256 and slot
identify each record. The bitcode identity is its SHA-256 and symbol spelling.

The version getter shares the exact 79-byte source definition at offset
6,913,879 with the native compiler record. The verifier reads the source
archive and compares its hash, extracted C hash and byte span against the
native manifest. The two recipes have different configurations and targets.
[Native record](../../../corpus/sqlite/equivalence/native-compilers/manifest.json) · [Reactor pin](../reactor.json)

The receipt describes build provenance and the selected symbol-to-slot
associations. It provides no instruction or CFG correspondence, compiler
correctness claim, or claim about runtime behavior. Imported functions,
linker-generated functions and linked code from other objects have no
association to the retained amalgamation bitcode in this receipt. The other
amalgamation symbols are outside the selected set.

## Reproduce

On x86-64 Linux with Python 3.11 or later, Bash, GNU coreutils, `unzip` and
`tar`, use the two pinned archives from the
[reactor instructions](../README.md#reproduce).

```bash
bash tools/sqlite-wasm/llvm-provenance/check.sh "$inputs"
```

The check builds twice in fresh directories, the second under a symlinked
temporary directory, with a 90-second limit per build. It compares the driver
trace and receipt to the committed versions and compares all three artifacts
byte for byte. The build checks the
existing source, SDK, compiler, linker and reactor pins. The check keeps
the binaries in a temporary directory and removes them on exit.

To inspect the intermediates and build records locally:

```bash
stage=$(mktemp -d)
bash tools/sqlite-wasm/build.sh "$inputs" --retain-llvm "$stage"
python3 -B tools/sqlite-wasm/llvm-provenance/receipt.py "$inputs" "$stage"
```
