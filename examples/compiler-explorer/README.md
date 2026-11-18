# Compiler explorer fixtures

Inputs of [`tools/compiler-explorer`](../../tools/compiler-explorer/README.md).

* `programs/`: the staged C examples (`hello.c`, `msort.c`, `fft.c`, `lisp.c`).
* `builds/<program>/<O0|O2>/`: gcc 13.3.0 (`gcc:13.3.0@sha256:1d71f0f3…`, the image of
  `tools/c-tv`) with `-g -S -std=c11 -fno-asynchronous-unwind-tables -fdebug-prefix-map=/src=.`,
  run with no network: the assembly, `RECEIPT.json` (command, versions, hashes of `cc1`, `as` and
  `ld`, source and assembly SHA-256) and `run.json` (that assembly linked by the same image against
  its glibc and run once: exit code and output). Running is a test, not a proof.
* `compiles-to/<file>/<O0|O2>/`: `objdump -d -w` listings of the objects of
  `examples/compiles-to` (the bytes the Lean statements are about), with their receipts.
* `manifests/`: one problem per build (and function), written by `fixtures.py manifests`.

No Lean statement covers the four programs: the C elaborator behind
`Silmaril.Project.CompilesTo` has no loops, calls, pointers, floating point or I/O. They show the
debug-information links and the execution tests only; their obligations are `unsupported`. The
checked examples are `straight.c` and `branch.c` of `examples/compiles-to`.
