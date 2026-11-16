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

**Provenance.** The `.text` is reproducible from `toy.S`: `build.sh` (with GNU as 2.44 and
GNU ld 2.44 when clang is absent) produces the same 60 bytes. The whole ELF file is not
reproduced byte for byte: the linker writes other metadata, which no theorem uses.
`build.sh` also builds `toy-native` (gcc) for `wasm-sim reduce --run --native`, which compares the
simulator with native execution on four inputs (a test, not a proof).
