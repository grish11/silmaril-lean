# Quoted reactor seven-byte varint reader

`SqliteWasm.getVarint_sevenByte` applies to slot 434 of the pinned
reactor. It requires seven readable input octets in the initial callee
memory, with six continuation bits set and a terminal seventh octet.
The eight-byte output span must be in bounds and may overlap the input.

Given the explicit runtime slot, instance, code, signature, and memory
bindings, `Varint.read?` returns the seven base-128 digits as a UInt64
and advances to `src.toNat + 7`. The Core call reaches i32 7 in the
original caller frame. Its exact store is the original store with the
eight-byte little-endian result spliced into callee memory 0.

The VC generator checks the quoted body, including the signed load
at offset six and the third `0x4000` correction. The six- and seven-byte
proofs import the same Wasm-local accumulator and call-transfer lemmas.
The accumulator tracks the finalized prefix and the newest octet,
whose continuation bit remains until the next correction.

The decoder consumer checks the exact slot-434 function record against
`originalDecode` and the original-byte Function/Code selector. The
behavior theorem concerns the seven-byte branch and takes the runtime
bindings as premises.

## Reproduce

```sh
bash tools/sqlite-wasm/check-get-varint-seven-byte.sh ARCHIVE_DIR WORK_DIR
```

The script rechecks the six-byte theorem and its ordinary import. The
seven-byte consumer imports all seven reader proofs, uses the theorem at
the high endpoint, and kernel-replays overlong zero, 4398046511104, and
562949953421311. In all three replays the seven input octets lie inside
the eight-byte output span. The replay checks the entire final store,
including the separate caller memory, and the restored caller frame.

For the decoder binding, build the
[whole-module fixture](whole-module/README.md#reproduce) in the same work
directory and run the ordinary decoder consumer.

```sh
root="$(realpath WORK_DIR)/lean"
cp tools/sqlite-wasm/GetVarintSevenByteDecodeImport.lean "$root/SqliteWasm/"
LEAN_PATH="$root${LEAN_PATH:+:$LEAN_PATH}" \
  lake env lean -j1 -s 131072 -DautoImplicit=false -E warning --root="$root" \
  "$root/SqliteWasm/GetVarintSevenByteDecodeImport.lean"
```
