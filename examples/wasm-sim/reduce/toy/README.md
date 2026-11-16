# The reduction toy

`toy.S`: `f(a, b) = sum_to(a) + dbl(b)` in x86-64 assembly. `toy.elf` (committed) is it linked
at `0x401000`; `reduce.toml` poses its System V contracts; `out/` is the output of

```sh
wasm-sim reduce examples/wasm-sim/reduce/toy/reduce.toml -o examples/wasm-sim/reduce/toy/out --granularity insn
```

(the files in `out/` regenerate byte for byte), and `insn/dbl.wat` is quoted by
`Silmaril.Sim.Reduce.Toy.Dbl` (`dblModule`).

**What the theorems are about.** `Silmaril.Sim.Reduce.Toy` states the toy's problems over `code`,
the 60-byte `.text` of `toy.elf`. `scripts/check-wasm-sim.py` (`make check`) checks that the
committed `toy.elf` has exactly that `.text`.

**Provenance (reproducible build receipt).** `build-pinned.sh` rebuilds `toy.elf` **byte for
byte** (sha256 `518e07bb1a311210f28af5fc5cf9f263bbc2670b23852a712237c3c3c32d1010`) in a pinned
container: `debian:trixie` at digest
`sha256:9c6e381421d0f48d1b8133e573f33c185ee16cbf505eda9c4a8a4791b25ea8a6` (Debian 13.7),
`clang-19` 1:19.1.7-3+b1 and `binutils` 2.44-3. Without clang, `build.sh` falls back to GNU as;
that gives the same 60-byte `.text` (what the theorems use) but a different ELF file, because GNU as
aligns `.text` to 1 byte where clang aligns it to 4.

`build.sh` also builds `toy-native` (gcc) for `wasm-sim reduce --run --native`, which compares the
simulator with native execution on four inputs (a test, not a proof).
