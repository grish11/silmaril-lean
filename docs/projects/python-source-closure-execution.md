# Executing fixed positional Python closures from source

The [source runner](../../Silmaril/Languages/Python/Compile/Closure/Run/Thms.lean)
links the analyzed source to the Core closure executor. Each value is an
integer literal or a name read. A nested function definition stores a
closure with the linked code reference and ordered captures. A positional
call assigns its result to a named local or cell. Each function has a
final value return or falls through to an implicit `None` return. Source
lowering erases a `pass` before either exit. It consumes no Core steps and
preserves the frame layout and lexical child order. Fallthrough emits
the existing executor return with a literal `None` operand. A nested
call writes that value to its destination before resuming the caller.
Bare `return` and explicit `None` syntax remain outside this source profile.

A standalone zero-argument call to a resolved name uses the executor's
discard destination. The caller resumes with its saved frame and the
callee's residual heap. The call preserves the lexical child index.
For these statements the compiler requires an empty argument list and a
bare name callee. The module-function runner also allows resolved global
reads, which use the current module binding at invocation.

Message-free body assertions lower to the existing executor assertion
when the test passes the ordinary runner operand check. They preserve
the continuation's lexical child paths and code keys. The executor
continues on truth and uses ordinary defined error delivery on failure.
The assertion operand profile covers Boolean literals, integer literals,
resolved reads, and a single comparison of the form `name == integer_literal`.
This comparison requires the exact integer AST node and reuses the ordinary
name resolver for locals, cells and, in the module-function runner, globals.
Core reads the name once, preserving lookup errors, then compares exact
integers and treats Booleans as 0 or 1. The modeled `None` and function values
compare unequal to an integer. Calls, arithmetic, chained comparisons and
user-defined equality are outside this profile. In a module invocation, a
failed body assertion is raised as `AssertionError`.

The ordinary body profile also accepts message-free literal-string membership
and non-membership assertions against `name.__code__.co_freevars`. The linker
attaches the sorted names of the checked lexical captures, including forwarded
captures, to the layout-matched code definition. The executor compares the
literal code points with that tuple after reading the current name. An alias
uses the same code reference and cells. This metadata profile covers ordinary
function paths with distinct ASCII capture identifiers and excludes class paths
and synthetic `super` and `__class__` captures. A nonfunction receiver or
unprofiled definition gives a distinct executor fault. The source profile
admits the tuple lookup inside these assertions.

The `co_cellvars` source form accepts message-free literal-string
non-membership on a resolved bare name. Its code definition records the
sorted names of the checked function's owned cells. Forwarded captures still
contribute to `co_freevars`. A definition with captured parameters has no
`co_cellvars` tuple in this profile because their observable ordering differs
between CPython 3.7 and 3.13. The executor retains the literal code points and
uses the same frame, heap and function identity through the test.
The source and linker also recognize message-free
`assert "<literal>" in name.__code__.co_names` in an ordinary function.
The name-table evidence is indexed by the linked code key and layout. It
models the order in which CPython 3.7.3 and 3.13.5 intern name operands
in `exec` mode at optimization level zero. It records global loads,
the two attribute loads of this form, and the assertion-failure operation.
The 3.7.3 tuple includes the synthetic `AssertionError` name. The 3.13.5
tuple uses a dedicated opcode for that branch. Repeated names keep their
first index, and each nested body has its own table. Unsupported code
shapes have no checked tuple. Execution of `co_names` assertions still
requires a Core metadata read and stops at the executor lowering boundary.

Successful lowering retains the source translation and preserves the
definition, layout and parameter destinations at every emitted code key.
Body lowering succeeds exactly when the independent translation judgment
has a derivation.
The entry starts with a fresh heap and binds the supplied arguments by
position. The runner produces the actual labelled Core path, with an
explicit state at the fuel limit.

The conformance check feeds Python source files through AST intake and
compilation and checks the resulting Core execution against CPython. It
covers a forwarded nonlocal write observed by the original caller,
arity and noncallable errors, and an unbound capture propagated out of the
callee. It also checks a live one-step prefix and the diagnostic for
arithmetic in an executor body.

```sh
make check CHECK_TARGETS=+Silmaril.Languages.Python.Compile.Closure.Run.Thms
```
