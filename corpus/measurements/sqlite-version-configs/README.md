# Delivered SQLite versions and configurations

These are actual public upstream release inputs and built ELF bytes, not version labels over one source tree. [artifacts.csv](artifacts.csv) maps every counted row through version → upstream Fossil source ID/archive SHA256 → configuration → target triple → compiler/flags → optimization → stripping → artifact/receipt/census/strip pair. [summary.json](summary.json) counts exact content hashes independently from rows.

| Upstream release | Delivered targets | Configurations | Levels | New ELF rows | Unique ELF hashes |
| --- | --- | --- | --- | ---: | ---: |
| [3.46.1](3.46.1/summary.json) | x86_64, AArch64 | default, FTS5+RTree, small | O0, O2 |48|40|
| [3.50.4](3.50.4/summary.json) | x86_64, AArch64 | default, FTS5+RTree, small | O0, O2 |48|40|

| [3.54.1](3.54.1/summary.json) | x86_64, AArch64 | default O2, FTS5+RTree, small | O0, O2 |40|36|

All136 new rows/116 unique hashes/68 stripping pairs have actual bytes and source/recipe/tool/command/runtime/census receipts. All510 measured commands exited successfully. Version, archive, C source and Fossil source IDs differ genuinely. Some shell outputs are identical across configurations; row count does not count them as unique bytes. Source IDs are read from upstream C; exact runtime version observations are separate.

The default configuration enables threading. FTS5+RTree enables both extensions and actually exercises insert/search/range queries. Small disables threading, extension loading and default memory-status tracking, with recorded compile options. Both clean repeats and stripping forms pass the package smoke tests. Each repeated build uses its own initialized container and clean private workspace; those same two workers are reused across profiles. Full installed-package locks and immutable image IDs, sources, commands, flags, timings and decoder limitations remain in receipts.

The complete requested hierarchy has144 delivered rows/120 unique hashes:136 new rows plus8 retained existing default3.54.1O0 rows. [retained-existing.json](retained-existing.json) preserves their exact hashes, original lifecycle claims and receipts, with no new execution claim. New sources were compared byte-for-byte against members of each exact hash-verified upstream ZIP. The four new default3.54.1O2 unstripped library/shell hashes exactly match canonical bytes; canonical paths remain unchanged.

[container-pool-lifecycle.json](container-pool-lifecycle.json) preserves the actual complete lifecycle: exactly two independently initialized workers,34 successful new profiles, both workers removed successfully. The separate remaining-O2 stage starts only after this cleanup. [timings.csv](timings.csv) maps all510 measured commands to exact successful records with wall time, CPU time and peak RSS; host page caches were not reset and cache state remains unspecified. No fresh-container-per-profile claim.

No existing canonical/variant bytes are replaced. Public upstream source is under test; owned recipe/measurement code is separate. Public-domain dedications remain in included source headers. Census and runtime evidence establish no semantic equivalence, source binding, Lean proof or exhaustive testing. Full local make check was not run. Shared indexes/UI/DB/Lean remain owned by integration.
