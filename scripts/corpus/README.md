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

### Persistent bounded build workers

`variants.py` initializes exactly two independent workers per invocation, using the
immutable image ID resolved at startup. Both must match the **whole** committed
`corpus/toolchain/lock.txt` before any build. Initialization failure stops the run;
there is no retry loop. Each worker has 3 CPUs, 12 GiB memory and 256 PIDs; builds,
strips and tests execute serially. No third postprocessor is created. The controller
must run within the remaining 2 CPUs / 8 GiB of the task's aggregate budget.

Each container has a read-only root, private tmpfs `/build`, `/tmp`, `/root`, a
separate writable output mount, and read-only frozen recipes and archive cache.
Before every profile, recipes are rehashed, all writable workspaces (including
dotfiles and `/dev/shm`) are cleared and checked empty. `env -i` supplies a fixed
PATH, HOME, locale, timezone, epoch, job count and explicit profile options. Build
recipes verify the archive hashes independently in each worker, extract pristine
sources and configure from scratch. No ccache, host compiler configuration or
previous generated files enter a build. Host kernel/page caches are **not** reset;
measurements retain cache state `unspecified`.

Each repeat runs in its own container. ELF hashes and recorded input/command facts
must match. Stripping runs independently in those respective workers, followed by
stripped-byte comparisons and executable-section/address maps. Both repeat outputs
and their stripped forms run package smoke tests before publication. Frozen recipe
hashes, image ID, package lock hash, container IDs, creation commands, profile
sequence/reuse, environment, limits, measured commands and runtime results travel
with the receipts. This is clean-workspace reproducibility in independent
**persistent** containers, not a fresh-container repeat. Older receipts keep their
original lifecycle claims. Repeated `--configuration` options allow OpenSSL asm and
no-asm profiles to share the same bounded pool.

Pool lifecycle, package-lock dumps, failed commands and logs remain beneath
`--work`; completed profiles publish atomically to new variant paths. Containers
are removed at normal completion and on Python exceptions/SIGTERM. SIGKILL or host
failure can leave containers behind; the recorded IDs permit explicit cleanup.
`--resume` hash-checks completed outputs and included sources; it claims no new
execution for retained profiles. It initializes a new two-worker pool for this
invocation, rather than reconnecting to an earlier pool.

```sh
python3 -B -m unittest discover -s scripts/corpus -p 'test_*.py'
python3 scripts/corpus/variants.py --package openssl --configuration no-asm \
  --configuration asm --level O0 --level Og --level O1 --level O2 --level O3 \
  --resume --work /work/out/openssl-pool
```

The pool does not change `corpus/build-all.sh`, historical canonical artifacts,
formal coverage or catalog ownership. Runtime smoke tests are observations of
their recorded commands, not functional-equivalence or source-semantics proofs.

### Explicit profile subsets in one pool

Repeated `--profile CONFIGURATION:ARCH:LEVEL` selects exact tuples for one package,
without building Cartesian cross terms. It cannot combine with `--arch`,
`--configuration` or `--level`. Package configuration, architecture and optimization
are checked before Docker inspection. Defaults and ordinary matrix selectors stay
unchanged; selecting a tuple does not claim that it builds successfully.

```sh
python3 scripts/corpus/variants.py --package boringssl \
  --profile no-asm:aarch64:O0 --profile no-asm:aarch64:O2 \
  --profile asm:aarch64:O0 --profile asm:aarch64:O2 \
  --profile fips-shared:aarch64:O0 --work /work/out/boringssl-aarch64
```

This example omits optimized FIPS_SHARED, a separately unsupported/failed pinned
GCC14 native configuration. It does not retry it or substitute another compiler.
All selected profiles share exactly two workers; clean repeats, stripping, runtime
tests and publication guards remain identical. A failure ends the invocation,
records the active profile as failed, and removes both workers without retry.

### Detached controllers and recovery

For a long build that must outlive its launching terminal/session, use
`background.py`. It starts the explicit command in a new POSIX session with
stdin closed, durable logs, an exclusive PID record and a shared two-CPU host
affinity cap. Successful launch is not successful completion. Inspect the
build's lifecycle and stage receipts; run the progress monitor detached too.

```sh
python3 scripts/corpus/background.py --record /work/out/build-job.json \
  --log /work/out/build-job.log -- python3 -B scripts/corpus/variants.py \
  --package openssl --configuration asm --work /work/out/openssl-asm
```

If the host controller was killed but both workers remain, `--resume-pool POOL`
and `--recover-work PROFILE_WORK` (with `--resume`) can reconnect **without
creating replacement containers**. Recovery requires an unpublished profile,
two idle original workers, the exact immutable image, original mounts/limits/
read-only root, and matching full package locks. It verifies the frozen recipes,
both successful measured builds and unchanged copied outputs before rerunning
all strip comparisons, runtime tests, receipt creation and census. Original
logs/timings remain; reconnection time, reason and controller hashes are recorded.
Already published profiles are retained by hash validation. Incomplete builds,
busy workers or mismatched identities are rejected for explicit investigation.
This does not claim a new clean build or a fresh container on recovery.

### Published Pages catalog

[Corpus](https://hiloopai.github.io/silmaril-lean/#/corpus) reads the same public
`project.sqlite` as the other project views. `make pages` backs up the freshly
checked public project database into a new output and adds corpus tables **before**
generating the HTML and its database size/hash. It does not publish a private base
database. `PAGES_SOURCE_REV` is also passed to the corpus generator, so artifact
links use the public pushed Git commit rather than a build-service checkout HEAD.
The deployment waits for actual corpus and compiler-viewer browser checks.

[Compiler integration](https://hiloopai.github.io/silmaril-lean/#/compiler) links
the existing static source/target fixture viewer and explains its coverage.
The full corpus is not automatically a set of compiler-explorer mappings or
semantic proofs; per-artifact/function statuses remain explicit.
