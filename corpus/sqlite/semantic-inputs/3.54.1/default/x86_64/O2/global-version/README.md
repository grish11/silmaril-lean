# Actual SQLite global version pointer source closure

This is a source projection from the existing saved SQLite 3.54.1/default/x86-64/O2 translation unit, containing the actual `sqlite3_version` definition and `sqlite3_libversion` procedure. `projection.json` pins the translation-unit byte spans and contextual original-source/macro spans. The actual preprocessed initializer is the seven-element character array for `3.54.1` including its terminating NUL.

`typed-ail.sexp` is the actual frontend result for `context.c`. `program.sexp` is the actual elaboration result; `runtime.sexp` retains the pinned public runtime used by that elaboration. No alternate procedure body or callee contract is supplied. The selected new elaboration branches handle direct integer-element array initializers and non-CHERI/non-PNVI/non-strict lvalue array decay, with actual element conversions, freshness and evaluation annotations. Other branches remain unsupported.

The existing canonical ELF getter is eight bytes at `0x13810`. It loads a pointer from the GOT slot at `0x10efc8`. The actual ELF relocation is `R_X86_64_GLOB_DAT`, symbol `sqlite3_version`, addend zero; the seven-byte object is at `0xed572`. These are distinct function, relocation and data evidence. Function `CodeAt` evidence does not establish a whole-ELF loader or dynamic-linker theorem. Any context for this getter must explicitly restrict the resolved GOT binding to this actual global; symbol interposition is not covered by observed native calls.

Local frontend/elaboration, initialized Core execution and native/machine executions are finite observations, not source refinement, compiler correctness, initializer correctness or semantic-equivalence proofs. This source closure alone is not a registered contextual coverage increment. Whole-TU preprocessing/frontend/build correspondence remains unproved. Other version/configuration artifacts are not interchangeable merely because their getter names match.

Reproduce only the source frontend/Core inputs (no ELF build):

```sh
lake env lean -DwarningAsError=true --run tools/corpus/reproduceSqliteGlobalVersion.lean
python3 tools/corpus/check_sqlite_global_version_inputs.py
lake env lean -DwarningAsError=true --run tests/cerberus/SqliteGlobalVersionExecution.lean
lake env lean -DwarningAsError=true --run tests/cerberus/SqliteGlobalVersionMachine.lean
python3 tools/corpus/check_sqlite_global_version_native.py
```

The source context uses fixed distinct function/GOT/global/caller-region addresses and arbitrary 64-byte caller payloads. It demands complete source memory equality after restoring only diagnostic `currentLocation`, and target preservation outside a zero-byte private frame. Post-startup initialization is computed from the actual saved initializer; adequacy of that bounded preparation as a real program-startup model remains unproved. Native and machine tests sample inputs; they do not prove those universal obligations.
