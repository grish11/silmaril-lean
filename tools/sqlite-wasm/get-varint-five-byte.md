# Quoted reactor five-byte varint reader

`SqliteWasm.getVarint_fiveByte` covers the five-byte branch of slot 434 in
the pinned SQLite reactor. The initial bytes at effective offsets zero
through three have their continuation bits set. The byte at offset four
terminates. The five successful lookups establish the readable input span
in the initial callee memory.

Under the explicit function-slot, instance, signature and callee memory
bindings and an eight-byte destination in bounds, the theorem proves both
results.

- `Varint.read?` returns the five radix-128 digits as a UInt64 and advances
  to `src.toNat + 5`.
- The Core call reaches i32 5 in the original caller frame. Its exact store
  is the initial store with the eight-byte little-endian result spliced into
  callee memory 0. The input may overlap that destination.

The existing VC generator checks the actual quoted reader. After the
fourth-byte correction, the next step shifts by seven, XORs in the fifth
octet and XORs `0x4000`. The Wasm-local
`VarintContinuation.appendAfterContinuation` lemma moves that last correction
to bit 7 of the preceding accumulator. The five-byte word proof combines it
with the earlier correction and the input byte conditions. The lemma is
also applicable to the recurring correction at the next three widths.
The behavior theorem concerns the five-byte path.

The decoder consumer uses `originalDecode` and `originalGetVarintFunction`
to check the exact slot-434 function record, including its locals and
body. The behavioral theorem takes the runtime instance bindings as
premises and imports `Silmaril.Formats.Sqlite.Varint.Defs` directly.

## Reproduce

```sh
bash tools/sqlite-wasm/check-get-varint-five-byte.sh ARCHIVE_DIR WORK_DIR
```

The ordinary downstream file imports all five reader proofs and exercises
overlong zero, 268435456 and 34359738367 with all five input bytes inside
the output span. It kernel-replays the largest value and checks the
complete configuration, including both memory mappings and the caller frame.

For the decoder binding, use the
[whole-module fixture](whole-module/README.md#reproduce) in the same work
directory and run:

```sh
root="$(realpath WORK_DIR)/lean"
cp tools/sqlite-wasm/GetVarintFiveByteDecodeImport.lean "$root/SqliteWasm/"
LEAN_PATH="$root${LEAN_PATH:+:$LEAN_PATH}" \
  lake env lean -j1 -s 131072 -DautoImplicit=false -E warning --root="$root" \
  "$root/SqliteWasm/GetVarintFiveByteDecodeImport.lean"
```
