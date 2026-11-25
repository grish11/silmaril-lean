# Quoted reactor six-byte varint reader

`SqliteWasm.getVarint_sixByte` covers the six-byte branch of the pinned
reactor's slot 434. It requires six readable input octets in the initial
callee memory, with five continuation bits set and a terminal sixth octet.
The eight-byte output span must be in bounds and may overlap the input.

Under the explicit runtime slot, instance, code, signature, and memory
bindings, `Varint.read?` returns the six base-128 digits as a UInt64 and
advances to `src.toNat + 6`. The Core call returns i32 6 in the original
caller frame. Its exact store is the original store with the eight-byte
little-endian value spliced into the callee's memory 0.

The VC generator checks the quoted body. The arithmetic proof uses
`VarintContinuation.appendAfterContinuation` at both occurrences of the
`0x4000` correction. The private accumulator invariant records the
finalized prefix and the latest octet with its continuation bit intact.
Each correction finalizes the preceding octet, and the terminal-octet
lemma gives the final value.

The decoder consumer checks that `originalDecode` and the separate
original-byte Function/Code selector agree on the exact slot-434 function
record. The behavior theorem concerns the six-byte branch and takes the
runtime bindings as premises. It imports the existing
`Silmaril.Formats.Sqlite.Varint.Defs`.

## Reproduce

```sh
bash tools/sqlite-wasm/check-get-varint-six-byte.sh ARCHIVE_DIR WORK_DIR
```

The downstream Lean file imports all six reader proofs. It checks overlong
zero and the canonical endpoints 34359738368 and 4398046511103 with all
six input bytes inside the output span. The largest value also has a
bounded kernel replay of the complete final configuration, including the
separate caller memory and the restored caller frame.

For the decoder binding, build the
[whole-module fixture](whole-module/README.md#reproduce) in the same work
directory and run the ordinary decoder consumer.

```sh
root="$(realpath WORK_DIR)/lean"
cp tools/sqlite-wasm/GetVarintSixByteDecodeImport.lean "$root/SqliteWasm/"
LEAN_PATH="$root${LEAN_PATH:+:$LEAN_PATH}" \
  lake env lean -j1 -s 131072 -DautoImplicit=false -E warning --root="$root" \
  "$root/SqliteWasm/GetVarintSixByteDecodeImport.lean"
```
