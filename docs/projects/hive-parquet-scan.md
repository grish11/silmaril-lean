# Hive partition scans over Parquet Arrow events

The input is an ordered manifest. Each partition supplies a validated nullable
tuple at the virtual [Hive schema](hive-typed-partitions.md) and an ordered list
of Arrow file traces at one common physical schema. `readFile` uses the
[Parquet reader](../../Silmaril/Formats/Parquet/Reader/Defs.lean) on an already
opened typed source and preserves its pull budget. `extendTrace` appends the
partition tuple to every row using the shared Hive row extension.
[Executable definitions](../../Silmaril/Formats/Hive/ParquetScan/Defs.lean)

## Order and terminal behavior

Within each partition, visit files in order. EOF advances to the next file.
An empty partition contributes no rows and permits traversal to continue. A
close, read error, or close error stops the whole manifest after all preceding
rows and the current file's emitted prefix. A manifest that exhausts all its
files emits EOF. The supplied file trace determines whether the last pull
reaches EOF or closes a live cursor.

`scanRowwise` runs the shared Arrow filter and projection on the augmented
manifest. `scanHoisted` tests the virtual tuple once per reached partition.
It projects kept batches directly and discards the rows of false or unknown
partitions while retaining their terminal outcome. The theorem
`scanHoisted_equivalent` compares the collected schema, ordered nullable rows
and terminal outcome. Batch boundaries can differ. The assembly laws
`assemble_eof` and `assemble_stops` expose composition and the stopping rule.
[Theorem header](../../Silmaril/Formats/Hive/ParquetScan/Thms.lean)

The model starts after a successful file open. It consumes supplied Arrow
traces, including traces from filtered files. Skipping an open or read could
hide a failure and permit rows from later files to appear. Such an optimization
would require an independent successful-read and terminal-outcome contract.
Filesystem discovery, file opening, and byte decoding are outside this layer.

## Checks

```sh
lake build --wfail +Silmaril.Formats.Hive.ParquetScan.Checks
make check CHECK_TARGETS=+Silmaril.Formats.Hive.ParquetScan.Checks
```

The closed Lean cases exercise multiple files and partitions, empty partitions
and batches, duplicates, projection including width zero, false and unknown
predicates, a filtered file with a read error, retained rows before a failure,
EOF, early close and close failure. [Checks](../../Silmaril/Formats/Hive/ParquetScan/Checks.lean)
