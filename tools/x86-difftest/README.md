# x86-difftest: the Str9G model against this processor

Untrusted tooling. It tests the hand-written x86-64 semantics `Silmaril.X86.Str9G.step`
(FS-relative forms, CET, `rdtsc`, atomics, `cmpxchg`, SSE2 moves, `rep stos`) against the host CPU.
These are tests, not proofs.

* `difftest.py` generates instruction cases from 77 templates. It assembles each with GNU as, runs
  it natively between a prologue and an epilogue that load and store all registers, flags and XMM
  registers, and writes `out/cases.txt`.
* `Check.lean` replays every case with `Str9G.step`, from the same initial state, and compares
  registers, defined flags, XMM registers and the memory buffer.
* `StrlenRun.lean` runs glibc's `__strlen_sse2` (412 bytes of a pinned `libc.so.6`) on
  `Str9G.step` from a System V call, on 300 random strings, including first blocks that cross a
  page. Each result must equal C `strlen`, with the callee-saved registers and `rsp` restored.

```sh
tools/x86-difftest/run.sh insn --per 300 --seed 7
tools/x86-difftest/run.sh strlen DIR   # DIR/ubuntu_2_39_0ubuntu8_9/libc.so.6, the pin of docs/projects/ptmalloc.md
```

## Results

| Run | Host | Result |
| --- | --- | --- |
| `insn --per 300 --seed 7` | x86-64 Linux under gVisor (kernel 4.19.0-gvisor), gcc 14.2.0, GNU as 2.44 | 23,100 cases, **0 mismatches**: atomic 1,800, fs 11,700, cet 600, rdtsc 300, cmpxchg-eq 300, sse2 8,100, stosd 300. 300 cases fault natively (`incsspq` raises #UD without CET), and the model has no step for them, as it should |
| `strlen` | same host; `libc.so.6` sha256 `3a15d668…98bf` | 300 runs, **0 failures** |
| `insn --per 300 --seed 7` (earlier run, before publication) | Intel Core i7-8700, Linux 6.8, gcc 13.3.0, GNU as 2.42 | 23,100 cases, 0 mismatches; same `strlen` result |
