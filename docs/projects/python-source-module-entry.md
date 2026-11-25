# Python module-entry source profile

The source checker reads the actual module scope analysis and retains a
typed global reference for each read and write. Readers and assignment
targets carry their name and exact access, including an explicit
`global` declaration. An uninitialized name read still carries its key so
the runtime can give the defined lookup outcome.

The plan contains single-name assignments and assertions in source order.
Operands include signed integers, booleans, global reads, addition, floor
division and a single equality comparison. Bare `global` and `pass`
provide the corresponding scope and statement evidence. The plan supplies
operations to the module runtime, which gives the initialized store and
execution outcomes.
[Definitions and translation laws](../../Silmaril/Languages/Python/Compile/ModuleEntry/Thms.lean)

The regression emits Lean from Python source and verifies the global
access witnesses, action order and the diagnostic for an assertion
message.

The source runner accepts an initial namespace and builds the Core module
entry using the analyzed spelling of each name. Its correspondence law
matches the exact completion, visible trace and residual namespace.
The execution regression compares CPython and Lean on initialized reads,
overwrites, assertion failure, an unbound read and arithmetic failure.
[Runner contract](../../Silmaril/Languages/Python/Compile/ModuleEntry/Run/Thms.lean)

```sh
make check CHECK_TARGETS=+Silmaril.Languages.Python.Compile.ModuleEntry.Thms
make check CHECK_TARGETS=+Silmaril.Languages.Python.Compile.ModuleEntry.Run.Thms
```
