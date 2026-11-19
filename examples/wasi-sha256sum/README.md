# A WASI preview1 `sha256sum`

`src/lib.rs` is `sha256sum` with no operand as a WASI preview1 core module: no libc, no
dependencies, and exactly four imports, `wasi_snapshot_preview1.{fd_read, fd_write, fd_close,
proc_exit}`. It makes the calls of silmaril's reference program `Sys.refMachine` in the same
order: `fd_read(0, [32768])` until a read returns no bytes, `fd_write(1, [rest of record])`
until the 68-byte record `hex(SHA-256(stdin)) ++ "  -\n"` is written, `fd_close` 0, 1, 2,
`proc_exit(0)`. An error answer traps.

| file | size | SHA-256 |
|---|---|---|
| `dist/sha256sum.wasm` | 2092 | `8aeedc3495370d82f08ef926a3da049f37dc28657218d4ba54a3a00b6c32b724` |

Build: `./build.sh` (Rust 1.99.1 with the `wasm32-unknown-unknown` target; release profile,
`opt-level = "s"`, LTO, stripped). Two builds in different target directories gave the same
bytes. Check against GNU `sha256sum`: `wasmtime run dist/sha256sum.wasm < FILE` prints the same
line as `sha256sum < FILE` (checked on the empty input, a short text and 100000 random bytes).

The Lean side is `Silmaril.Sim.WasiBridge.Cli.Sha256sumSys` (`wasmFile`, `Task.wasiRefinesRef`,
`wasiSha256sum_sat`): the module's preview1 trace semantics is a parameter until the core
semantics of a module against a preview1 host is a definition.

Licence: MIT, as the rest of this repository. The SHA-256 constants are from FIPS 180-4.
