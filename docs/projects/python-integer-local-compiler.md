# Python source to an integer local frame

The [integer-local compiler](../../Silmaril/Languages/Python/Compile/Locals/Thms.lean)
accepts one undecorated parameterless function with scalar assignments,
terminal `if` statements and value returns. Every branch ends in a return.
Expressions use integer literals, local reads, addition, integer floor
division and operand-valued `and` or `or`. The result consists of the lowered
[Core frame](python-integer-local-frames.md) and evidence from the actual
source scope analysis.

Slots follow the order in which bindings were first collected. Each
lowered read or write carries a bounded index, the source name found at
that index, and the analyzed local-access equality. Each successful
compilation carries independent expression and body translation
derivations. The runner theorem gives the exact result and final store
specified by its lowered code at the Core frame budget.

The regression covers a local write and read producing 42, a read before
assignment raising UnboundLocalError, and floor division by zero
preserving the preceding local write. A source name resolved outside the
local slot set causes a compile-time diagnostic.

The AST regression compares CPython and the compiled Core frame on branch
selection, short-circuit evaluation and errors raised during a condition.

The Core frame starts with all slots unbound. Argument binding, closure
construction and calls require the next Core interface.

```sh
make check CHECK_TARGETS=+Silmaril.Languages.Python.Compile.Locals.Thms
```
