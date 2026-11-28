# SQLite Track E coverage inventory v1

Import `Silmaril.Machine.SQLite.Architecture.All` for the diagram and the four
groups. Each row names a public import and a theorem to inspect with Lean
`#check` or `#print`. The diagrams, component theorems, and finite fixtures
have different observation boundaries. [Diagram source and graph guide](architecture.md) ·
[Build, replay, and hosted evidence](replay-v1.md)

## Upstream identities

| Reference | Exact identity |
| --- | --- |
| Architecture figure | Fossil SHA3-256 `702a00612bfe17b8728e1e4cff7dd19a15d605095d78fb1994fd92f3b0b32015` for `pages/arch.in`. Its SHA-256 is `6b5084fd9c58a14b1284b66b8b239bf87057064985370fe8b269d4e34a0158a2`. The guide records the rendered SVG and HTML digests. [Source bytes][arch] |
| SQLite 3.54.1 split source and test code | All implementation links below use mirror commit `57520227c95396ce39ba6ecaac8d475b78dd3964`, whose `manifest.uuid` is Fossil check-in `555e07ef33f69a0957d24d8e555b702464a131d6f1607f4c3c1e4551e8e6ca76`. [Commit][release] · [Fossil identity][uuid] |
| SQLite 3.54.1 generated C API and amalgamation | `SQLITE_VERSION_NUMBER = 3054001`. Archive `sqlite-amalgamation-3540100.zip` has SHA-256 `0a9c8e34352dad46006aa82836d5383bff9dc6bc9ce5a60553c05aa30e6ad1f9`. Vendored `sqlite3.h` has SHA-256 `d6c84557261893439b341d2e6c35187ae3ea24fbfd843ad94616f72d89242b8c`. [A header and build inventory](../sqlite-track-a/header-inventory/README.md) · [Vendored hashes](../../../corpus/sqlite/upstream.sha256) |
| Rendered SQLite file-format documentation | `fileformat2.html` fetched 2026-11-26 had SHA-256 `905067afacc30583c9ee86778b532094cc1830c7ec7b5f019bcfd2eb9ded97a2`. The website URL is live. The format implementation references are pinned to the release above. [File format](https://www.sqlite.org/fileformat2.html) · [B-tree][btree] |
| Rendered VM opcode reference | `opcode.html` fetched 2026-11-26 had SHA-256 `7f08cf2ddaca9e8df4dcbbca2d1ef72dce48069daa1e78866f02c527914e43df`. [Opcodes](https://www.sqlite.org/opcode.html) · [VDBE at the release pin][vdbe] |

The release and the diagram have independent identities. The release links
identify the SQLite mechanisms the inventory compares with the Lean models.
The theorems quantify over the Lean definitions in their import closure. To
verify the vendored bytes, run `(cd corpus/sqlite && sha256sum -c upstream.sha256)`
from the root. The header inventory gives the archive URL and preprocessing
recipe. [Source extraction](../sqlite-track-a/header-inventory/README.md)

## Diagram, groups, and leaves

| Diagram item | Public import | Checked statement and scope |
| --- | --- | --- |
| Diagram | `Silmaril.Machine.SQLite.Architecture.Thms` | `Architecture.nodes_complete`, `containment_wellFormed` and `edges_wellFormed` check the finite inventory of four groups, eleven boxes and nine drawn arrows. Calls and semantic dependencies are the relations documented in the graph guide. |
| Core | `Silmaril.Machine.SQLite.Core.All` | Re-exports Interface, SQL Command Processor and Virtual Machine. |
| Interface | `Silmaril.Machine.SQLite.Interface.Thms` | `Interface.Connection`, `Session` and `Prepared` reuse D3 state. `prepare_bind_execute` combines successful text preparation, slot-one binding and compiled execution with the exact D3 prepared result and post-connection. `execute_iff` gives the D3 invocation relation under parsed-text and compatibility premises. `execute_cold_warm` has the additional storage premises below. [Public C API source][api] · [Prepare][prepare] · [Bind and step][vdbeapi] |
| SQL Command Processor | `Silmaril.Machine.SQLite.CommandProcessor.Execute.Thms` | `CommandProcessor.prepare_iff` characterizes successful preparation through the parser and D3 planner. `execute_iff` relates one complete execution to `CatalogExecutor.denote`, including D3 scope, resolution and bind outcomes. Valid lexical/grammar representation and VM compatibility restrict the theorem. |
| Virtual Machine | `Silmaril.Machine.SQLite.VirtualMachine.Thms`, `.VirtualMachine.Traced.Thms`, `.VirtualMachine.Mutable.Thms`, `.VirtualMachine.Concurrent.Thms` (same prefix) | `VirtualMachine.step_iff`, `run_trace` and `pointProgram_lookup` cover fixed code and a supplied rowid snapshot. The traced VM records ordered events and `Traced.runWithTrace_result` preserves the fixed-code run result. The other laws cover preconditions over eligible snapshots, a string-code rewrite simulation, and finite scheduler correspondence. [VDBE source][vdbe] |
| SQL Compiler | `Silmaril.Machine.SQLite.Compiler.All` | Re-exports Tokenizer, Parser and Code Generator. |
| Tokenizer | `Silmaril.Machine.SQLite.Tokenizer.Thms` | `Tokenizer.tokenize_iff` characterizes complete lexical success for the admitted ASCII tokens. `lexes_render` has a canonical-token premise. [SQLite tokenizer][tokenize] |
| Parser | `Silmaril.Machine.SQLite.Parser.Thms` | `Parser.parse_iff` checks complete grammar recognition and `represents_print` checks printing for a well-formed two-name AST. [SQLite grammar][grammar] |
| Code Generator | `Silmaril.Machine.SQLite.CodeGenerator.Bytecode.Thms` | `CodeGenerator.prepare_iff` gives the D3 resolution/admission relation. `run_compile` gives exactly the label and optional looked-up cell, assuming the supplied VM table represents the target when the parameter is bound. An unbound plan yields an empty result without entering the VM. [SELECT lowering][select] · [WHERE lowering][where] |
| Backend | `Silmaril.Machine.SQLite.Backend.All` | Re-exports B-Tree, Pager and OS Interface. |
| B-Tree | `Silmaril.Machine.SQLite.BTree.Thms` | `BTree.opened_read` relates the named, live, granted read to both typed interpreters. `catalog_cold_warm` connects a caller-designated, admitted packed 512-byte rowid leaf to a numbered-page lookup, ordered D4 batch and storage-erased D3 result. The lookup yields an integer on a hit and no row on a miss. [SQLite B-tree][btree] |
| Pager | `Silmaril.Machine.SQLite.Pager.Thms` | `Pager.observeInsert_ofAccess`, `commit_reopens` and `sync_failure_preserves_database` describe the admitted one-slot insert and retirement. Re-exports A's handled read agreement. [SQLite Pager][pager] |
| OS Interface | `Silmaril.Machine.SQLite.VFS.Thms` | `VFS.open_success` identifies the live named handle, mode and file-map frame. `open_error_preserves` preserves the map on rejection. Re-exports the modeled read-only and read-write handler laws. [VFS ABI][api] · [Dispatch][os] |
| Accessories | `Silmaril.Machine.SQLite.Accessories.All` | Re-exports Utilities and Test Code. |
| Utilities | `Silmaril.Machine.SQLite.Utilities.Thms` | `Utilities.varint_roundtrip` recovers every `UInt64` from its emitted bytes at an admitted position and advances by the encoded width, between one and nine. The existing record and leaf codecs use `Varint.encode`. [SQLite varint][util] |
| Test Code | `Silmaril.Machine.SQLite.TestCode.Thms` | `TestCode.Fixture.check_iff` checks equality against an independently supplied expected observation with decidable equality. Checked examples include a truncated varint and rejection of an eight-position reader on a nine-byte fixture. [Lean fixtures](../../../Silmaril/Machine/SQLite/Accessories/Checks.lean) · [Upstream test sources][tests] |

## Behavioral coverage

**Checked** denotes a general Lean theorem within the specified model.
**Bounded** identifies restrictions on its operations, inputs or observations,
or individual checked regressions. **Unmodeled** lists gaps in this integration.

| Surface and reference | Checked and bounded coverage | Unmodeled |
| --- | --- | --- |
| Public API and session, `sqlite3_prepare_v2`, `sqlite3_bind_int64` [API][api] | **Checked, bounded.** `Interface.prepare_bind_execute` carries D3's resolved plan and session. `bindInt64_one` replaces slot one; `bindInt64_outOfRange` preserves the prepared value. Execution is one-shot. Text and VM/transfer errors are distinct from D3 replies. | Native handles and ABI, ownership and lifetime, resumable `sqlite3_step`, reset, finalize, repreparation, callbacks, and other bind/column APIs. |
| Handle lifetime and default VFS borrow [API][api] | **Checked, bounded.** `Handle.Thms` models close-only open errors, empty prepare, busy and zombie close, owner-checked disposal, and registered default VFS borrowing. [Contract and replay](handle-resources.md) | Native handle and struct refinement, full SQL command admission, registration updates, and VFS lifetime across unregistration. |
| Public allocation, `sqlite3_malloc`, `sqlite3_free`, `sqlite3_realloc` [API][api] | **Checked, bounded.** The `Allocator.Thms` header specifies initialized allocation, ownership and usable size over the shared allocation history. `realloc_success_lookup`, `realloc_failure_preserves` and `frames` cover lifetime changes and preservation of other resources. [Contract and replay](allocator-resources.md) | Byte contents and realloc copying, allocator choice and rounding, native addresses, and initialized API implementation refinement. |
| SQL and resolution [Tokenizer][tokenize] · [Grammar][grammar] · [Resolver][resolve] | **Checked, bounded.** One complete `SELECT column FROM table WHERE rowid = ?1` with unquoted normalized ASCII names, an optional final semicolon, D3 catalog checks, and a single selected cell or miss. [Compiler guide](../sqlite-point-select.md) | Full SQL, quoted and qualified names, joins, aggregates, ordering, writes, optimizer correctness and native parser correspondence. |
| Types and schemas [Value API][vdbeapi] · [Mem][vdbemem] · [Schema][build] | **Checked, bounded.** `Silmaril.Semantics.SQLite.Relational.All` exposes `Value.toSql_ofSql`, `ColumnType.strict_apply_eq_ok_iff`, `TableSchema.findColumn_eq_some_iff`, `CheckedTable.rowsEquivColumns` and `CatalogExecutor.execute_eq`. D1–D3 model five storage classes and selected affinity, named columns, checked rows, catalog restrictions and point evaluation. D2's cross-table foreign-key certificate is separate from the D3 snapshot. [D handoff](../sqlite-track-d/handoff-v1.md) | General coercions, collations, native Mem ownership, schema changes and constraints during general writes. |
| Relational results [SELECT][select] | **Checked.** `Silmaril.Semantics.Relational.All` gives typed rows, query relations and finite stream observations. `QueryRel.Refines.observe` preserves refinement under projection. D3's `SelectResult.toOutput` materializes the zero-or-one-row result. [C contract](../relational.md) | A full SQL evaluator or a general refinement of native SQLite into C's query model. |
| Bytecode and observations [VDBE][vdbe] | **Checked, bounded.** Named operand forms and a six-instruction point path over a caller-supplied database/root and signed key. `observe_pointProgram` gives the ordered row and successful halt for a found table. `Traced.runWithTrace_result` preserves the fixed-code result; `wp_snapshots` quantifies over eligible immutable snapshots for a fuel-bounded successful run. `Mutable.run_represents` preserves erased code and the result for the modeled String8-to-String rewrite. | Complete opcode admission, arbitrary EXPLAIN decoding, transaction or Pager effects in compiled VM execution, allocator or encoded-string behavior, and native VM refinement. |
| File format and B-tree pages [File format](https://www.sqlite.org/fileformat2.html) · [B-tree][btree] | **Checked, bounded.** `Silmaril.Formats.Sqlite.File.Header.Frame.Thms` exposes `parseHeader?_frame` for equal first 100 bytes past the length guards. `Silmaril.Formats.Sqlite.Record.Admission.Thms` exposes `parse?_admission` for bounded headers, legal serial types and exact payload consumption. B's `leaf_represents` and `page_lookup_run_iff` connect the designated decoded SQLite rowid leaf to a height-zero generic tree. [B read bridge](../sqlite-track-b/read-bridge.md) | Whole-file/catalog consistency, arbitrary SQLite interior traversal, index execution, overflow coverage for the designated-leaf bridge, balancing and multipage edits. Generic represented-tree lookup laws have their own all-height scope. |
| Pager and repeated reads [Pager][pager] | **Checked, bounded.** `Read.Adapter.interpretations_agree` threads backing, cache and exchanges. `pagerTwice_readOnly_cold_warm` and `Bridge.execute_cold_warm` use the admitted same-page read and an owned vacant slot. The warm read reuses the installed bytes. `Bridge.execute_corresponds` covers an individual bound call, including typed read failures. [A reading map](../track-a-reading-map.md) · [D4 read bridge](../sqlite-track-d/read-bridge.md) | General page cache policy, eviction, writeback, concurrent paging and whole-file refinement. |
| Transactions and rollback journal [Pager][pager] · [B-tree transactions][btree] | **Checked, bounded.** `SqliteVfs.TrackA.Write.run_follows_schedule` checks the selected preimage write, journal sync, database write, database sync and journal deletion sequence. `Pager.commit_reopens` and `sync_failure_preserves_database` observe reopen or the injected journal-sync failure on the canonical two-page insert profile with the matching owned slot. [A write contract](../sqlite-track-a-write.md) · [Backend guide](../sqlite-backend-components.md) | Transaction setup, rollback playback, savepoints, hot journals, multi-file commit, WAL/SHM, durability and crash recovery. Sync replies constrain modeled order. |
| Threading and locking [Threading entry points][main] · [Mutex][mutex] · [File locking][unix] | **Checked, bounded.** `VirtualMachine.Concurrent.simulate_ordinary_iff` and `simulate_ub_iff` relate finite replay to ordinary observations and races. `catastrophic_eq_top_iff` characterizes collapse at a possible race. The model uses one SC generation slot and one optional mutex. `Pager.LockGrant` is a caller premise about a named live handle. | Native connection mutexes and VFS file lock transitions, isolation, busy/retry logic, SQLite thread scheduling, fairness and liveness. |
| URI filenames [URI parser and open][main] | **Checked, bounded.** `VFS.parseOpen`, `open_success` and `open_error_preserves` cover plain basenames and opt-in `file:NAME` with at most `mode=ro` or `mode=rw`. The requested mode bounds the result, and the file must already exist in the map. | Authorities, percent encoding, paths with separators, filename canonicalization, additional parameters, global URI settings and native open flags/fallback. |
| VFS [API][api] · [Dispatch][os] · [Unix implementation][unix] | **Checked, bounded.** `Silmaril.Machine.SqliteVfs.Thms` gives `readOnly_lawful`, `readWrite_lawful` and `backing_trace_bounds` for the bounded typed handlers. `bad_not_readOnlyProfile` distinguishes a well-typed short read that violates zero fill. Read/Page and role-qualified write effects retain selected exchanges. [Backend guide](../sqlite-backend-components.md) | Native VFS registration and OS/filesystem refinement, permissions, platform locking, mmap, randomness and time. |
| Utility and test code [Varints][util] · [Upstream tests][tests] | **Checked, bounded.** The codec consumes one to nine bytes; the fixture theorem covers a single supplied observation. Checked regressions exercise selected text, VM, file and backing outcomes through their published modules. | General collation, PRNG, allocator, printf, and coverage or formalization of the upstream SQLite test harness. |

### Compiled execution and file reads

`Interface.execute_cold_warm` uses one D3 binding and resolved target. The caller
supplies `Bridge.Bound` and `Bridge.ColdLeaf` for a classified invocation,
successful resolution, slot-one signed key, caller-designated packed 512-byte
rowid leaf, live readable range, owned vacant slot, image/backing agreement, and
successful leaf decoding. `Bridge.Projected` requires that the second field read
by D4 agrees with D3 at the bound key. The leaf decoder admits an integer in
that field, so this storage profile returns an integer on a hit and no row on a
miss. The compiler address supplies that same decoded table, with ordered
rowids and actual selected cells paired to D3 rows by
`CodeGenerator.EntryRepresents`. The broader compiler snapshot contract
also covers hits with a present SQL NULL.
[Leaf decoder](../../../Silmaril/Formats/Sqlite/TableLeaf/Defs.lean) ·
[Compiler guide](../sqlite-point-select.md)

The VM runs once on the supplied table snapshot. Its reply agrees with each
D4 call's result and post-connection after storage erasure. The D4 batch
retains both calls in order, with the actual backing and installed slot, one valid
full-page exchange on the cold read, and no additional exchange on the warm
read. The representative rollback-journal insert has separate Pager
observations and write-access premises.
[Interface theorem](../../../Silmaril/Machine/SQLite/Interface/Thms.lean) ·
[Backend theorem](../../../Silmaril/Machine/SQLite/BTree/Thms.lean) ·
[D4 handoff](../sqlite-track-d/handoff-v1.md)

[arch]: https://sqlite.org/docsrc/raw/702a00612bfe17b8728e1e4cff7dd19a15d605095d78fb1994fd92f3b0b32015
[release]: https://github.com/sqlite/sqlite/commit/57520227c95396ce39ba6ecaac8d475b78dd3964
[uuid]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/manifest.uuid
[api]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/sqlite.h.in
[prepare]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/prepare.c
[vdbeapi]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/vdbeapi.c
[vdbe]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/vdbe.c
[tokenize]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/tokenize.c
[grammar]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/parse.y
[select]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/select.c
[where]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/where.c
[resolve]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/resolve.c
[vdbemem]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/vdbemem.c
[build]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/build.c
[btree]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/btree.c
[pager]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/pager.c
[main]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/main.c
[mutex]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/mutex.c
[os]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/os.c
[unix]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/os_unix.c
[util]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/util.c
[tests]: https://github.com/sqlite/sqlite/tree/57520227c95396ce39ba6ecaac8d475b78dd3964/test
