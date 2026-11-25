# Closed Python source to Core

Import [Compile.Closed.Thms](../../Silmaril/Languages/Python/Compile/Closed/Thms.lean).
The executable compiler calls the Python source scope analyzer and accepts
a module containing one undecorated zero-argument function whose body
returns integer literals or exact addition. The target is the entered
[Core body](python-core.md). Module creation, looking up the function and
calling it belong to later semantics.

The compiler has distinct diagnostics for scope analysis, module shape and
unsupported expressions. The [translation
judgment](../../Silmaril/Languages/Python/Compile/Closed/Defs.lean) describes
the accepted syntax and target tree. A second source judgment gives the
integer result without invoking the compiler or the Core runner.

- `compile_iff` characterizes successful compilation by scope acceptance
  and the translation judgment.
- `rejects_iff` characterizes each reported diagnostic. A scope diagnostic
  retains the analyzer's exact result. Module shape requires scope
  acceptance, and expression shape requires a valid outer function shape
  for which the translation judgment has no witness.
- `returns_exists` gives a source result for every compiled body.
- `initial` authorizes entry to the compiled body in the addition profile.
- `observes_iff` identifies the Core return observations with source results.
- `run_exact` gives the executable completion at sufficient fuel.

The regression parses a file containing a function returning `1 + 2` through
the [source AST emitter](python-source-scope.md), compiles its constructors
and observes `3` through the Core runner. The constructor-level tests also
distinguish scope rejection, a dynamic call, an unsupported operator and the
empty module.

The [executable conformance harness](../../tests/languages/python/source-scope/check_intake.py)
uses ten original MIT-licensed fixtures. It compares six actual integer
returns with CPython, including nested addition and values above 64 bits.
Four other fixtures check Lean's scope, module-shape or expression-shape
diagnostics. The JSON summary lists the execution and rejection counts
and each observation. The harness runs only the six fixed return fixtures
in CPython.

```sh
make check CHECK_TARGETS=+Silmaril.Languages.Python.Compile.Closed.Thms
```
