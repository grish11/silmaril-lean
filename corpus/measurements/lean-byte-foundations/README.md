# Pinned Lean byte-foundation baseline

Ten existing modules elaborated and kernel-checked with the repository's exact
Lean nightly (see [toolchain version](toolchain-version.txt)), `-j 1`,
`warningAsError=true` and `autoImplicit=false`. All ten passed. This is a real,
measured foundation closure used by the corpus, **not** a whole-artifact parse,
function-decomposition check, full library build, or semantic proof baseline.

One sequential repeat, with warm host file caches declared; module outputs were
written to a fresh directory. Sum of subprocess wall times: **5.167 s**. Maximum
per-process peak RSS: **1,666,808 KiB**. These exclude toolchain acquisition and
wrapper startup/hash recording. Each module includes elaboration and kernel
checking together; those costs were not separated. Dependencies generated earlier
in the sequence were imported by later modules. There is no cold-cache comparison.

The command, module/input hashes, repository revision, toolchain version hash,
runner, CPU/RSS and exit status are in each linked receipt. Transient absolute
paths in the receipts identify the actual run, not required installation paths.
Use the modules in the order below and an isolated `LEAN_PATH` output directory.
With the exact pinned `lean` on PATH, each subprocess command is:

```sh
lean -j 1 -DwarningAsError=true -DautoImplicit=false \
  -o "$LEAN_PATH/$MODULE.olean" "$MODULE.lean"
```

| module (ordered) | wall seconds | peak RSS KiB | receipt |
|---|---:|---:|---|
| `Silmaril/Data/IncludeBytes/Types` | 0.200 | 564412 | [run](runs/12426e16-aa8f-48e4-8e62-156949bf2620.json) |
| `Silmaril/Prelude/Bytes/Digits/Defs` | 0.272 | 568464 | [run](runs/a5a2978c-be25-4770-9d24-d6c509d247c0.json) |
| `Silmaril/Proofs/Prelude/Bytes/Digits` | 0.454 | 575152 | [run](runs/69262f73-dc59-4ca5-9c12-d536121003c6.json) |
| `Silmaril/Prelude/Bytes/Digits/Thms` | 0.195 | 562296 | [run](runs/47e2ab58-8ea9-4bd1-8efd-0f0132e2bcce.json) |
| `Silmaril/Prelude/Bytes/Defs` | 0.355 | 572896 | [run](runs/8cc1d1e3-e13f-4d8f-9d86-166d8c92e79e.json) |
| `Silmaril/Proofs/Prelude/Bytes/Basic` | 1.438 | 595748 | [run](runs/36c6c82e-61b3-4002-8493-733bd7c8aa45.json) |
| `Silmaril/Prelude/Bytes/Thms` | 0.234 | 570300 | [run](runs/ebcdd8a0-434f-4430-9609-e98d2f422050.json) |
| `Silmaril/Prelude/Bytes/Elab/Defs` | 0.595 | 925800 | [run](runs/d77a87d4-74b7-4f79-9254-5cfdde310db2.json) |
| `Silmaril/Data/IncludeBytes` | 0.653 | 855572 | [run](runs/36190fe1-5e7d-4022-921b-ca535e5a0cf2.json) |
| `Silmaril/Data/IncludeBytes/Kernel` | 0.772 | 1666808 | [run](runs/10f0daa5-3ace-417e-8410-5f04d6816221.json) |
