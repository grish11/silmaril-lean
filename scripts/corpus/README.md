# Corpus evidence and measurements

`census.py` reads every completed canonical and variant receipt, verifies each ELF's
SHA-256, and writes one JSON report per artifact. Run it in the pinned corpus
toolchain image; it needs native and AArch64 GNU binutils. It does not execute the
artifacts. The reports contain receipt identities, `DT_NEEDED`, SONAME, interpreter,
version requirements, imports, relocation types, TLS/IFUNC indicators, exact import
matches for selected ABI features, executable-section mnemonic counts, bounded
exact-mnemonic extension evidence, and syscall instruction sites.

```sh
corpus/toolchain/image.sh
docker run --rm --network host --cpus 8 --memory 32g \
  -e CORPUS_ANALYSIS_IMAGE_ID="$(docker image inspect --format '{{.Id}}' silmaril-corpus-toolchain:trixie-20251103)" \
  -v "$PWD:/repo:ro" -v /work/out:/out -w /repo \
  silmaril-corpus-toolchain:trixie-20251103 \
  python3 -I scripts/corpus/census.py --output /out/census
python3 -B scripts/corpus/test_census.py
python3 -B scripts/corpus/test_measure.py
```

This is tool-derived evidence, separate from Lean parsing/decomposition proofs and
machine semantic support. Linear decoding may interpret data as instructions. All
executable sections are listed, including sections with no disassembly output.
Decoded, undecoded and unreported byte counts stay separate. The extension
classifier is intentionally incomplete and publishes its allowlist in each report.
An empty match is not evidence that an extension is absent. A syscall site is not
a runtime observation; syscall numbers are left unknown. Imports are potential
dependencies, not demonstrated runtime use. Static dependencies, indirect calls,
signals, futex behavior and vDSO use need further analysis or observation.

`measure.py` runs one explicit command and writes a fresh UUID-named JSON record.
It records repository/input/tool hashes, command, target, declared cache state and
concurrency, runner capabilities and cgroup limits, wall time, child CPU time,
Linux peak RSS and exit code. Run it **inside** the container to measure the actual
tools: wrapping `docker run` measures full wall time but only Docker-client CPU/RSS.
`--repository-receipt` accepts the host's Git revision/dirty/diff hash as JSON when
the pinned container has no Git. Keep independent runners' records and merge files;
there is no shared writable measurement database. Concurrency is recorded, not
enforced by this wrapper. Use the container limits and tool-specific job limits.

Measure acquisition, compilation, ELF parsing, function extraction, decomposition
generation, Lean elaboration/kernel checks, project dump/export, SQLite generation,
and semantic problem/proof stages separately when they run. Do not infer a stage's
cost from an aggregate command, or claim a run for a stage that was not executed.

`db_benchmark.py` exports an existing SQLite database as SQL (optional) and replays
the SQL into a **new** database, checking SQLite integrity and reporting table
counts, SQL hash and materialization wall time. It never replaces the input.

```sh
python3 scripts/corpus/measure.py --stage sqlite-export-and-materialization \
  --output /work/out/runs --target host-sqlite --input INPUT.sqlite -- \
  python3 -I scripts/corpus/db_benchmark.py --database INPUT.sqlite \
    --sql /work/out/input.sql --output /work/out/replay.sqlite
```

For repeats, omit `--database` and replay the saved `--sql` into a different new
output. SQL and output databases retain the input's disclosure restrictions. This
benchmark measures SQLite materialization, **not** Lean elaboration, project
validation, canonical project SQL generation, or end-to-end regeneration. No ELF
byte-storage representation is changed by these tools.

## Corpus explorer database

`matrix.py` indexes completed canonical/variant receipts and checks every ELF hash.
`database.py` generates additive corpus metadata tables from that real inventory,
source mapping/context files, paired stripped mappings, census reports and measured
run receipts. ELF bytes remain in Git; the database records their paths and hashes.
No source semantics or TV statement is inferred from mapping metadata.

Variant census reports live under `corpus/census/variants/` with the full
project/version/configuration/architecture/optimization/stripping path. Generate
only those with `census.py --variants-only --output /out/census`; canonical report
paths stay stable. Each report names and hashes its exact receipt and ELF. The
catalog loads these reports for variants too and rejects a mismatching ELF hash;
it never substitutes a canonical artifact's report for a variant. Reports retain
linear-decoder coverage limits and distinguish static sites from runtime observations.

```sh
mkdir -p /work/out/corpus-site
python3 scripts/corpus/database.py --output /work/out/corpus-site/project.sqlite
make project-tool
build/bin/silmaril-project explore --db /work/out/corpus-site/project.sqlite \
  --out /work/out/corpus-site/index.html
python3 -m http.server --bind 127.0.0.1 --directory /work/out/corpus-site 8789
# Open http://127.0.0.1:8789/index.html#/corpus
```

The Corpus view filters delivered project/version/target/optimization/stripping
rows, links immutable Git artifacts/receipts, shows build/source identity,
dependency/extension evidence, source mappings, searchable function rows and
measured-stage receipts. It shows each canonical artifact's whole-file parse or
layout-only status separately. Measured variant checks are accepted only for their recorded ELF hash,
Decomp root, successful run and unchanged generated module hashes; generation alone
does not promote the status. The OpenSSL x86
libcrypto debug-twin mismatch stays explicit. Function rows include aliases.

For an existing project, pass `--base INPUT.sqlite`; SQLite backup copies its
snapshot to the **new** output before adding corpus tables. The input is never
modified. Existing project navigation remains available alongside Corpus. A
standalone catalog has dedicated Corpus/SQL navigation. Output databases may be
regenerated, not updated concurrently; no custom VCS/cache/sharding system exists.
The output retains all disclosure restrictions of its base. Do not publish an
internal base, its combined database, or screenshots containing internal content.

Browser checks use the actual generated database, including project-preserving
navigation when `combined.sqlite` is present:

```sh
node tools/silmaril-project/tests/explore/corpus.mjs /work/out/corpus-site /work/out/corpus.png
```

CI generates the real standalone catalog and a combined public fixture and runs
these Chromium checks. The view does not yet provide a full multiversion build
matrix, source code rendering, or instantiated TV
and binary-equivalence problem pages. Zero statement counts remain explicit.

## Bounded table certificates and explicit variant generation

With `--max-table-entries`, `elf-staged emit-reader` now checks symbol and RELA
records in modules of at most 128 entries when a table exceeds the requested
threshold or 128 entries. `EntriesAt` composition, linked string-table identity,
entry size and exact record count assemble a `BodyIs` fact; `parses_assemble`
then proves the whole-file parse. No native computation is used to close these
facts. The generated candidates still require Lean elaboration/kernel checking.

```sh
python3 scripts/corpus/gen_variants.py \
  --artifact corpus/variants/cjson/1.7.19/default/x86_64/O0/unstripped/libcjson_utils.so.1 \
  --artifact corpus/variants/cjson/1.7.19/default/x86_64/O0/stripped/libcjson_utils.so.1 \
  --max-table-entries 16
# Add --check to compare regenerated headers. Build the reported Decomp roots with --wfail.
```

The low threshold forces the window path on the small checked pair. Exact artifact
paths are required; the generator validates the completed inventory and refuses
module-name collisions or overwriting files owned by another generator.

### Canonical optimization stripping pairs

`variants.py --level O2` explicitly builds two clean O2 outputs and their independent stripping pairs under `corpus/variants/<project>/<version>/<configuration>/<architecture>/O2/`. It follows the same pinned-image, clean-repeat, runtime-test and hash publication path as other levels. Defaults remain O0/Og/O1/O3; existing `corpus/elf` canonical bytes are unchanged. This option is a recipe capability, not a delivered O2 stripped artifact claim. Configuration `asm` still requires exactly OpenSSL and distinct configuration paths. Example (when container initialization is available):

```sh
python3 scripts/corpus/variants.py --package openssl --configuration asm --level O2 --arch aarch64 --work /work/out/openssl-asm-o2
```
