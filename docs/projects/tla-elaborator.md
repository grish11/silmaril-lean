# Scalar TLA+ surface elaborator

Import [`Silmaril.Logic.Temporal.TLA.Elaborator.Thms`](../../Silmaril/Logic/Temporal/TLA/Elaborator/Thms.lean).
`Elaborator.elaborate` takes a `Surface.Module`, an explicit list of available
standard-module identities, and a `Signature` giving the sort of every
`VARIABLE`. It returns a checked module or a `Diagnostic`. On a checked
module, select a nullary Boolean operator by its case-sensitive name.

- `statePredicate` accepts constant and state-level bodies. `stepPredicate`
  also accepts action-level bodies and reads state-level bodies at the source.
- `stateDenotation` and `actionDenotation` return the corresponding General
  TLA denotations. Kernel predicates also provide executable decisions.
- `signature.scope` indexes a state coordinate by its name and a proof that
  `signature.lookup name = some sort`. `signature.noRigid` supplies the empty
  outer rigid environment. Literal-set witnesses extend that environment
  locally and are shared by both endpoints of an action.

[Surface AST](../../Silmaril/Logic/Temporal/TLA/Surface/Defs.lean) · [Semantic kernel](tla-semantic-kernel.md)

## Checked fragment

| Surface form | Rule |
|---|---|
| `VARIABLE` groups | All and only declared names need a caller-supplied `Int` or `Bool` sort. State coordinates range over the full Lean carrier. |
| Nullary identifier definitions, including `LOCAL` and aliases | Each body sees only preceding declarations and the resolved standard environment. `LOCAL` names can be selected inside this same module. Bodies may have scalar results, and selected predicates must have Boolean results. |
| Scalar literals and references | Natural numerals denote integers. `TRUE` and `FALSE` are built-in Boolean names. A variable, bound name, or previously defined nullary operator is referenced without arguments or selectors. |
| Scalar operators | `=` and `#` require matching sorts. Boolean negation, conjunction, disjunction, implication, equivalence and nonempty junction lists require Boolean operands. Integer unary minus, `+`, `-`, `*` and order comparisons require the `Integers` import. Infix synonyms of supported operators follow SANY. |
| `IF … THEN … ELSE …` | The test is Boolean and branches have the same scalar sort. Both branches are checked, and all three subexpressions contribute to expression level. |
| `e'` | `e` is at most state level. Priming reads the entire expression at the target and produces an action-level expression. Another prime on that result is rejected, including through aliases. |
| `\E name \in { … } : body` | One fresh rigid name, one nonempty set enumeration, and a Boolean body. Elements have one sort and are natural numerals, unary minus on numerals with `Integers`, or Boolean literals. |
| `a := b` | With the verified identity of the pinned `Apalache` library supplied and `Apalache` named in `EXTENDS`, this is same-sort equality. Either operand may be any supported expression. |

The checker visits every unit, including unused definitions. It reports
conflicting names, including conflicts with built-ins and imported public
names, and rejects arguments on nullary references. Definition-body errors
carry the enclosing definition name. The parser is responsible for producing
lexically valid identifiers and the AST shapes in its grammar contract.

Unsupported forms include `ASSUME`, `CONSTANT`, `RECURSIVE`, `INSTANCE`,
submodules, proof units, parameterized and symbolic definitions, qualified and
higher-order references, `LET`, strings, decimals, nonliteral or empty
quantifier domains, other quantifier forms, and composite values such as
functions, sequences and records. `EXCEPT`, `@`, `ENABLED`, `UNCHANGED`,
action brackets, temporal operators and fairness are also outside the fragment.

`:=` denotes a constraint on one fixed pair of valuations. For example,
`x' := y /\ y' := x` reads both right-hand sides at the source. A coordinate
omitted from the action is unconstrained at the target. The step predicate is
raw. Clients can add bracket stuttering explicitly with
`Kernel.Predicate.bracket` and choose the observation that it compares.

## Resolving imports

The caller attests that each permitted `StandardModule` identity resolves to
the corresponding library in the [pinned Apalache distribution](https://github.com/apalache-mc/apalache/releases/tag/v0.62.4).
The caller handles search paths and checks that local files do not replace
these libraries. The elaborator checks that every `EXTENDS` name has a supplied
identity and that no import is repeated or names the source module itself.
Only the listed `EXTENDS` entries participate in name lookup.

`Integers` provides the integer operations, including those exported through
its `Naturals` dependency. `Apalache` provides `:=` through its definition
`__x := __e == __x = __e`. Its `LOCAL INSTANCE Integers` does not provide
arithmetic to importing modules. The other supported imports are `Sequences`,
`FiniteSets`, `TLC` and `Variants`. Their exported identifiers are reserved
when imported, and their operators have no denotations in this fragment.
The pinned libraries have distinct public names in this profile. User-defined
libraries and standalone `EXTENDS Naturals` are outside this resolver.

[Apalache definition](https://github.com/apalache-mc/apalache/blob/7954daf7563a69cce9d0b89c8542e40bf46f7c6e/src/tla/Apalache.tla) · [Distribution checksum and fixture provenance](../../tests/semantics/tla-quint/README.md)

## Parser integration and checks

Use the unmodified [BoundedCounter](../../tests/semantics/tla-quint/BoundedCounter.tla)
and [BitPair](../../tests/semantics/tla-quint/BitPair.tla) exports. Pass the
parser's `Surface.Module` directly to the bridge and supply the following
arguments, after resolving the standard libraries as described above.

| Export | `Signature` | Initial / step operators |
|---|---|---|
| BoundedCounter | `[("n", .int)]` | `q_init` / `q_step` |
| BitPair | `[("x", .int), ("y", .int)]` | `q_init` / `q_step` |

The parser should keep all six `EXTENDS` names, declaration order and nullary
operator bodies. Keep `:=` as `Expr.infix (.symbol ":=")`, prime as
`Expr.postfix .prime`, and `TRUE` and `FALSE` as ordinary zero-argument
identifier references. BitPair's existential is `Expr.rigidQuant .exists`
with one bounded group whose `.names` contains `flip` and whose domain is
`Expr.setEnum`. Parentheses need no separate node. The type comments are
outside the surface tree. The signature in the table supplies their sorts
explicitly.

```lean
def elaborateQuint
    (source : Silmaril.Logic.Temporal.TLA.Surface.Module)
    (signature : Silmaril.Logic.Temporal.TLA.Elaborator.Signature) :
    Except Silmaril.Logic.Temporal.TLA.Elaborator.Diagnostic
      (Silmaril.Logic.Temporal.TLA.Kernel.StatePredicate signature.scope ×
        Silmaril.Logic.Temporal.TLA.Kernel.StepPredicate signature.scope) := do
  let checked ← Silmaril.Logic.Temporal.TLA.Elaborator.elaborate
    [.integers, .sequences, .finiteSets, .tlc, .apalache, .variants] signature source
  return (← checked.statePredicate "q_init", ← checked.stepPredicate "q_step")
```

Use the state domains and ordering from [oracle.json](../../tests/semantics/tla-quint/oracle.json)
with `Kernel.Bounded.initials` and `Kernel.Bounded.transitions`. The kernel
adequacy theorems `mem_initials` and `mem_transitions` relate these computed
lists to the General TLA denotations on the supplied domain. The Lean examples
check complete lists for both handwritten ASTs, prove their raw step equations
for arbitrary integer coordinates, and check a Boolean module where an
unconstrained target coordinate stays free. The public source-lift theorem
connects the two selection modes for every successfully selected state
predicate.

```sh
lake build --wfail +Silmaril.Logic.Temporal.TLA.Elaborator.Thms \
  +Silmaril.Logic.Temporal.TLA.Elaborator.Examples
```

[Lean regressions](../../Silmaril/Logic/Temporal/TLA/Elaborator/Examples.lean)
cover AST-to-denotation behavior and rejection cases. Concrete byte-to-AST
integration awaits the parser. General TLA+ source-language correctness and
specifications with fairness are outside these results.
