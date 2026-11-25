# Quoted reactor four-byte varint reader

`SqliteWasm.getVarint_fourByte` checks the four-byte branch of
`sqlite3GetVarint` at slot 434 in the pinned reactor. The first three
bytes at effective offsets zero, one and two have their continuation
bits set. The byte at offset three terminates. The four successful
lookups establish the readable span in the initial callee memory.

With the explicit function-slot, instance, runtime type and memory
bindings and an eight-byte destination in bounds, the theorem proves:

- `Varint.read?` returns
  `(((a % 128) * 128 + b % 128) * 128 + c % 128) * 128 + d` as a UInt64,
  and the next offset is `src.toNat + 4`.
- The Core call reaches i32 4 in the original caller frame. Its exact
  store is the initial store with the eight-byte little-endian splice
  into callee memory 0. The destination may overlap the four input bytes.

The existing VC generator runs on the actual quoted function. The
word proof moves the quoted `0x10204000` correction to the continuation
bits of the first three bytes before proving the radix-128 result. The
branch uses immediate load offsets, and its count calculation is modular
i32 arithmetic. The call rule transfers the checked path to the explicit
slot, memory and caller frame in the statement.

`originalGetVarintFunction` connects slot 434 with the original
Function/Code record. The separate decoder consumer applies
`originalDecode` and checks that the module's slot 434 has the same
complete function record, including the body used here. This theorem
covers one branch under explicit runtime bindings.

## Reproduce

From the repository root:

```sh
bash tools/sqlite-wasm/check-get-varint-four-byte.sh ARCHIVE_DIR WORK_DIR
```

The ordinary downstream file imports all four reader proof modules. It
exercises overlong zero and both edges of the canonical four-byte
interval, 2097152 and 268435455. All four input bytes overlap the output.
It also kernel-replays the latter boundary through the actual slot-434
call and checks its exact result and store. The short-input replay has
three continuation bytes, a missing fourth byte and an in-bounds
destination. The functional reader returns `none`, and that call traps
with its store and caller frame intact.

To check the decoder link, build the components listed in the
[whole-module reproduction](whole-module/README.md#reproduce) in the same
generated directory. Then run:

```sh
root="$(realpath WORK_DIR)/lean"
cp tools/sqlite-wasm/GetVarintFourByteDecodeImport.lean "$root/SqliteWasm/"
LEAN_PATH="$root${LEAN_PATH:+:$LEAN_PATH}" \
  lake env lean -j1 -s 131072 -DautoImplicit=false -E warning --root="$root" \
  "$root/SqliteWasm/GetVarintFourByteDecodeImport.lean"
```
