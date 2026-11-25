# Linking lowered Python closure bodies

The [closure linker](../../Silmaril/Languages/Python/Compile/Closure/Link/Thms.lean)
converts the [body compiler's](../../Silmaril/Languages/Python/Compile/Closure/Body/Thms.lean)
lexical paths to dense numeric keys in preorder. The entry function has
key zero. Closure instructions carry the child key, expected layout and
ordered capture operands. Each code-table entry pairs a body with its
positional parameter destinations.

The linker proves that the table paths equal the compiler's distinct path
list. Every emitted reference resolves at its intended lexical path and
layout. The regression dispatches an outer function and its nested caller
using the actual emitted code table, then reads the bound argument and
captured value from the callee frame. Body evaluation and continuation
dispatch are supplied by the enclosing machine.

```sh
make check CHECK_TARGETS=+Silmaril.Languages.Python.Compile.Closure.Link.Thms
```
