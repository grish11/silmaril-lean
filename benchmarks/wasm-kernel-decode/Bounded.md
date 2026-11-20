# Packed envelopes, bounded bodies

`Silmaril.Wasm.Binary.Packed.Bounded.decode?` consumes the header, section ids,
and size LEBs from a length-checked `KBytes`. Each section body goes to the
existing Core reader on just its own bytes, and must consume them exactly.
The reference reader's frame laws transfer these local runs to the exact
offsets in `Core.Decode.readModule`. The section loop checks order and EOF;
finalization checks function/body arity, data count, and data index use.

An optional list of code-entry end offsets (relative to the **start of the
code section body**, including its vector count) partitions the code payload.
The decoded packed count must equal the number of offsets. Offsets must advance
without crossing the section end, every entry must consume its entire slice
under the original `readCode` (including its size and locals cap), and the last
entry must reach the section end. The plan is never evidence on its own.

`Bounded.decode_sound` transfers a successful result to the full equation
`Core.decode? source.toByteArray = some decoded`. There is no converse or
failure equivalence here: custom sections are explicitly unsupported and a
bad plan can reject valid bytes. Most payloads still materialize their local
bytes. The single-passive-data proof is a separate path for large data. The
compiled Core implementation and runtime import closure are unchanged.

```sh
lake build --wfail +Silmaril.Wasm.Binary.Packed.Bounded.Thms
lake env lean -DwarningAsError=true benchmarks/wasm-kernel-decode/BoundedRegression.lean
python3 -I benchmarks/wasm-kernel-decode/run.py /tmp/wasm-bounded \
  --mode bounded --seconds 15 --memory 4096 --runs 1 \
  --cases empty-check lrat bodies-64 bodies-512 data-4k data-1024k
```

`kernel.csv` records separate processes for each proof, with the same imports,
quoted output, source bytes, and exact final proposition. The fast baseline
includes `decodeF`'s transfer to `Core.decode?`. The bounded proof checks the
offsets generated during preprocessing. `fixtures.json` pins every input;
large fixtures are generated, not stored in the repository.

## Recorded run

November 19, 2026, x86-64 Linux, repository toolchain. One run per case;
wall time includes imports. GNU `time` reports peak RSS; 4096 MiB is Lean's
allocator limit, **not** an OS RSS limit.

| Fixture | List slice | `decodeF` + transfer | Bounded |
| --- | ---: | ---: | ---: |
| `empty-check` | 4.30 s / 1.97 GiB | 3.20 s / 1.97 GiB | 3.20 s / 1.96 GiB |
| `lrat` | memory limit | memory limit | memory limit |
| `bodies-64` | 6.72 s / 2.91 GiB | 6.69 s / 2.91 GiB | 3.42 s / 2.06 GiB |
| `bodies-512` | memory limit | memory limit | memory limit |
| `data-4k` | 5.07 s / 2.08 GiB | 4.55 s / 2.08 GiB | 5.45 s / 2.08 GiB |
| `data-1024k` | memory limit | wall timeout | memory limit |

Three additional runs of `bodies-64` (`--runs 3 --cases bodies-64`) gave
median wall times of 6.62 / 6.25 / 3.42 s and median peak RSS of 2.91 / 2.91 /
2.06 GiB respectively. This is an end-to-end reduction on this input, not a
general throughput or large-module speedup. On LRAT and 512 bodies, bounded
framing alone can be checked, but bounded *full* proofs still exceed the
limit. On 1 MiB passive data, use the separate passive-data certificate.
