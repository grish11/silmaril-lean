# Starlark module publication and imports

The profile follows the Bazel-team core specification at
`c0af0ea03dc90d3bbc021394b693e6957cc15030`. Raw `spec.md` has SHA-256
`9e1e2b52717512968270bc99ca79aa8c9014df99a9befd0b47eed59c7c848597`.
[Module execution][modules] · [Load statements][loading]

`Silmaril.Languages.Starlark.Modules.Thms` exposes the resolved entry point
`initializeModule`. It checks argument-list legality and conflicting global
and file names before allocating slots. It executes top-level commands in
order. `TopCode.assignExpr` writes one global after evaluating a resolved RHS,
and `TopCode.evalExpr` evaluates a resolved expression and discards the value.
Both admit nested calls with keyword and spread operands, conditional
expressions, and short-circuit operators in the [direct expression profile][expressions].
Runtime errors retain operand effects without writing the assignment target
or running later commands. Existing atomic commands, definitions, calls,
and loads with named aliases use the same lifecycle. Temporary slots used
by call lowering and file-local imports remain outside the export list.

The entry point assumes resolved bindings, the list of declared globals,
single assignment of explicit globals, and legal load identifiers. The
[source adapter](#resolving-module-declarations) collects the scopes for an
admitted normalized AST.
[Definitions](../../Silmaril/Languages/Starlark/Modules/Defs.lean)

The host supplies a pure catalog of already published modules. It determines
how labels are interpreted. All modules in a catalog share the same heap
and the same linked function-declaration table. An imported value retains
its address, so calling an imported closure uses that closure's original
global slots. A missing catalog entry and a missing exported name are
distinct failures. Private import names are rejected during validation.
A single load resolves all its requested exports before binding their aliases.
[Load statements][loading] · [Lexical calls](starlark-functions.md)

A new module begins with fresh slots and no inherited active iterators.
Successful completion freezes all global values, including private ones,
before publishing the public export table. Runtime failure returns the
updated heap with the caller's scope and iterator context restored. The
failure path publishes no module and performs no publication freeze.
A caller supplies both the initial heap and any prepublished imports.
The heap may retain unreachable allocations.
[Module execution][modules] · [Reachable freezing](starlark-lists.md#reachable-freezing)

`runs_iff_runCommands` proves exact agreement before publication, including
the module and file namespace and the shared heap at the first failure.
`initializes_iff_initialize` extends agreement through the publication
boundary, comparing the export table or error and the entire residual
state after restoring the caller. Both proofs compose independent command
sequencing with `Exec`; its native expression rules derive calls and callee
bodies independently of the direct denotation. The module rules and
denotation share validation, namespace entry, the pure catalog contract,
and publication or failure restoration. Calls start with the finite linked
declaration table and remove the active declaration on descent.
[Operational rules](../../Silmaril/Languages/Starlark/Modules/Operational/Defs.lean) · [Theorem header](../../Silmaril/Languages/Starlark/Modules/Thms.lean)

## Resolving module declarations

`Modules.Resolve.resolve` takes normalized source commands and returns a
checked `Modules.Source` and linked declaration table. Module commands cover
single-name and [nested name-pattern assignment][pattern-assignment], [simple subscript assignment][subscript-assignment],
[integer subscript `+=`][augmented-subscript], expression statements, `def` and
named `load` imports. Function bodies add nested `def`, sequencing, `if`, `pass` and
`return`, as well as `for` loops with `break` and `continue`.
Signatures represent the positional, keyword-only, `*args` and
`**kwargs` classes used by the existing binder. Operands use the
[existing source expression profile][source-expressions], including the Lean
expression quotation.

The resolver collects globals and load aliases across the file, and
parameters and assigned names across each function body. A lexical binding
shadows outer names throughout its block. Undefined names fail statically
even in skipped code. A forward reference resolves to the slot but fails
dynamically if read before its assignment or load. Duplicate module bindings
and load/global collisions are rejected before execution.

For standalone destructuring, `Statement.assignTarget` resolves each name
leaf to a function slot and `Command.assignTarget` resolves each leaf to a
module global. The resolver collects those names before analyzing any RHS.
Both contexts also accept `assignTargetCompExpr` with the same target and
a `CompExpr` right-hand side. This form also accepts subscript leaves
whose receiver and index use the ordinary resolved expression grammar.
Only identifier leaves join the enclosing lexical block.
The module command uses the shared direct binder in source order. A failed
initialization retains earlier heap effects, including partial writes into
its slots, and follows the existing failure path without publication.
[Pattern semantics][pattern-assignment] · [Source assignment fixtures](../../Silmaril/Languages/Starlark/Modules/Resolve/Checks.lean)

The `assignListComp` and `assignDictComp` forms in `Statement` and
`Command` resolve comprehensions assigned to a name. Only that destination joins the
enclosing block. The first iterable uses the enclosing scope and the
remaining clauses resolve with all generator names local to the
comprehension. Quoted expressions can supply the pattern, iterable,
filter and yield ASTs, including dictionary key/value pairs. Resolved module
commands enter the same body
path as function assignments, then use the ordinary publication rules.
[List comprehension semantics](starlark-functions.md#list-comprehension-assignment) · [Dictionary comprehension semantics](starlark-functions.md#dictionary-comprehension-assignment)

The normalized `CompExpr` adapter allows comprehensions in call operands,
conditional and short-circuit operands, collection displays, and index
and slice reads within return values, assignment RHSs for names and
nested name patterns, operands of standalone simple and integer
augmented subscript stores, function-local integer augmentation, and
parameter defaults.
The first and later iterables and filters and the heads of a comprehension
use the same broader placement grammar.
Both selected and skipped AST positions are resolved before execution.
The emitted body evaluates only reached operands, preserves their order
and keeps prior shared heap effects on failure.
[Expression placement](starlark-functions.md#comprehensions-in-checked-expression-positions)

A loop target belongs to the whole function block. The resolver collects
all target names before resolving the iterable and body in that block. Thus
`for x in x` reads the function's `x` before any iteration writes it. The
last assignment to the target is visible after the loop, and an empty
loop performs no target write. Loops emit `Body.forInExpr` and use
the existing validation of `break` and `continue` in each function, including
skipped code and nested definitions. Tuple and list patterns with lexical
name leaves enter through `Statement.forInTarget`, for example
`.forInTarget starlark%[(x, [y, z])] starlark%[rows] .pass`. The resolver
rejects non-name leaves even in skipped code. A single identifier can use
`Statement.forIn`. The module command type admits
only top-level forms permitted in this profile.
[For statements in the pinned spec][loops] · [Resolved loops](starlark-functions.md#calls-inside-loops) · [Source loop fixtures](../../Silmaril/Languages/Starlark/Modules/Resolve/LoopChecks.lean)

Defaults resolve in the enclosing scope. Function bodies use the function's
own parameters and locals, and each declaration captures the free slots its
body or nested definitions need. A definition passes those slots through any
intervening function. The evaluator runs defaults when it executes the
definition command and installs the closure only after they succeed.
`SourceParameter.defaultExpr` accepts the normalized `CompExpr` grammar.
An ordinary quoted `SourceExpr` coerces to a plain expression.
[Name binding in the pinned spec][names] · [Resolver](../../Silmaril/Languages/Starlark/Modules/Resolve/Defs.lean) · [Comprehension defaults](starlark-functions.md#comprehensions-in-parameter-defaults)

```lean
module

import Silmaril.Languages.Starlark.Modules.Resolve.Defs
import Silmaril.Languages.Starlark.Functions.Lowering.Quote.Defs

open Silmaril.Languages.Starlark.Modules.Resolve
open scoped Silmaril.Languages.Starlark.Functions.Lowering.Quote

def exampleModule : List Command := [
  .assign "seed" starlark%["definition scope"],
  .define "pick" { positional := [⟨"seed", some starlark%[seed]⟩] }
    (.ret (some starlark%[seed])),
  .assign "out" starlark%[pick()]]

def exampleResult := runModule exampleModule (fun _ => none) {}
```

This module exports `out = "definition scope"`. `runModule` reports
elaboration errors separately from runtime errors and uses the resolved
module initialization and publication rules. Supply the existing linked
table when catalog values can contain closures. Resolving another module
appends declarations and preserves the IDs already in that table. To use
the finite loader, clients assemble the manifest and link its resolved
sources to one table.

`checked_of_resolve` states exactly which checked source and declaration
table successful elaboration produces, including the globals in source order
and absence of compiler scratch slots. `initializes_iff_runModule` composes
the elaboration result with the resolved operational theorem. It compares
static rejection, execution outcomes, publication and the exact residual
state. This correspondence shares the elaborator and starts at a normalized
AST with legal identifier spellings. A separate
[mixed assignment theorem](starlark-functions.md#mixed-name-and-subscript-targets)
relates accepted targets and a bounded RHS to independent lexical rules.
The block collection theorem below supplies that environment and write
scope for its admitted forms. A separate theorem covers capture selection
and installation along a bounded nested function chain. Whole-module
elaboration against independent source rules and text parsing remain open.
Lambdas, general comprehension expression
positions, field leaves, store leaves in loop and comprehension targets,
and other augmented assignment forms remain outside this source fragment.
The pinned Starlark spec rejects slice assignment targets.
[Theorem header](../../Silmaril/Languages/Starlark/Modules/Resolve/Thms.lean) · [Lean source fixtures](../../Silmaril/Languages/Starlark/Modules/Resolve/Checks.lean)

Pinned Starlark-Go checks cover static and dynamic name errors, captures,
defaults, load aliases, and loop scope and control. Go rejects the
load-then-global collision and accepts the global-then-load order. The Lean adapter follows the
Bazel-team spec and rejects both.
[Pinned Go comparison](../../examples/starlark/scope/check.go) · [Name binding in the pinned spec][names]

### Lexical block collection

`ModuleBinders` and `BodyBinders` state which normalized commands and
statements declare names, with their occurrences in source order. The
load-free module subset covers name assignment, mixed patterns,
ordinary subscript stores, expression statements and definitions. The
function subset also covers pass, return, sequences and both branches of
a conditional. A definition binds its name in the current block. Its
parameters, defaults and body do not contribute binders there. A nested
block can be collected separately using the parent's read context.

In a mixed pattern, only a name leaf contributes a declaration. A
receiver, subscript index, RHS and comprehension generator contribute no
declaring occurrence in the surrounding block. `ParameterBinders` follows
the normalized parameter classes. `LocalBinders` keeps the first occurrence
of each other body binder. An assignment to a parameter reuses its slot.
`owned_read` selects a body binder's owned slot even before its first
assignment and even when an enclosing or global name has the same
spelling. An uninitialized slot fails when read.

`moduleBlock_eq` and `collectFunctionLayout_eq` prove the existing
compiler's collection and write-scope phases agree with the declarative
rules. `module_assignment_sound` and `function_assignment_sound` compose
with the independent mixed-assignment elaboration theorem and put each
resolved name leaf among the declared globals or owned slots. Assignment
elaboration still uses the bounded leaf and RHS grammar. The block rules
cover declaration occurrences only. Identifier, parameter, duplicate
global and runtime validation remain in the existing checked entry point.

The function collection theorem takes the parent context as input.
Whole-source execution, unproved binder grammar including load aliases
and loop targets, and broader leaf and RHS elaboration remain open.
[Block judgments](../../Silmaril/Languages/Starlark/Modules/Resolve/Block/Defs.lean) · [Theorems](../../Silmaril/Languages/Starlark/Modules/Resolve/Block/Thms.lean) · [Lean fixtures](../../Silmaril/Languages/Starlark/Modules/Resolve/Block/Checks.lean)

### Nested function captures

The capture theorem starts in a load-free module. The inner function
has required positional parameters and a body
consisting of `(name, receiver[index]) = rhs` followed by `return operand`.
The leaf and return operands use the bounded #3171 grammar. The RHS is a
plain operand or a single-generator list comprehension in that grammar.
`parent_layout` supplies the outer function's owned names and inherited
module globals from the proved block collector. The forwarding theorem
permits any finite number of intervening functions that define and
return their child, with required positional parameters at every level.

`BodyReads` gives the binding occurrences of the RHS, target and return,
in that order. `Selects` ignores owned parameters and locals. For a free
local, `Nearest` chooses the first enclosing block that owns the name.
The module rules resolve an otherwise unshadowed name to its global slot. It retains the first occurrence of
each free reference in the Lean declaration. The comprehension generator
contributes no free read of its own binding. `mixed_definition` connects
these rules to the exact declaration appended by the compiler. Go uses
cells for enclosing free variables and carries the module's global
dictionary separately. The Lean list represents just the module slots
that are read. Its order is a Lean representation property.

`define_installs` relates selected addresses in the defining activation
to the new heap cell and the binding holding its function reference.
Restoring the caller preserves that cell. `activate_selected` preserves
the installed addresses while allocating the callee's own slots.
Creation consults the slot address. Reading an uninitialized binding
through that address fails when invoked. `read_after_rebind` states that
a write by the slot's owner is then visible to that callee. A list store
through the captured value instead changes the list's heap cell. Both
observations agree with the pinned spec's free-variable references and
the pinned Go fixtures.

For each wrapper, `compile_chain` proves that the child definition's
capture demands feed the wrapper's own capture list. `nearest_route`
identifies the forwarding prefix up to the nearest local owner.
`global_route` carries the module-global reference through every
wrapper in the Lean representation. `child_installs` derives all of the
next child's slot addresses from the parent's installed captures and the
owned slots allocated at activation. `local_address` and `global_address`
preserve the original address through every successful creation and
activation on the corresponding route, including its local-cell tag.

The forwarding path starts from the source address and successful definition
and activation steps. It supplies the next child's capture slots from the
parent layout. The entry and argument bridge below derives the root
addresses, the live owned destination cells, and positional argument
preparation that can feed these steps.

The five-level fixture creates the leaf before the nearer owner rebinds
a list reference, then invokes it after escape. It also observes a
separately forwarded module slot before and after initialization. Lean
checks the emitted lists and runtime local-cell tags. The observable
results agree with pinned Go.
[Judgments](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Defs.lean) · [Forwarding judgments](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Forwarding/Defs.lean) · [Forwarding theorems](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Forwarding/Thms.lean) · [Lean fixtures](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Forwarding/Checks.lean) · [Pinned Go fixtures](../../examples/starlark/scope/check.go) · [Pinned definition semantics](https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#function-definitions) · [Go lexical selection](https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/resolve/resolve.go#L960-L990) · [Go shared cells](https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/interp.go#L642-L661)

### Checked module entry and positional binding

The independent load-free binder judgment supplies the module's global
list. Actual module entry allocates a fresh owned cell for each declared
global, initially unbound even when the caller has a populated heap.
An independently emitted root capture plan names only those globals.
`checked_root_definition` uses these facts to derive the root capture and
definition-target cells and its exact closure allocation. The proof
uses the supplied declaration lookup in the checked table.

`Assigns` pairs required parameters with evaluated positional actuals in
order. `Binds` accounts for success, a missing suffix, and surplus
arguments. The exact preparation theorem derives signature validity from
module validation. Successful preparation activates with the derived
arguments. Binding errors preserve the pre-dispatch state. For a root
definition immediately followed by preparation, the declaration lookup
also supplies its membership in the initial finite availability set.
`activated_cell` derives a live owned cell for each declared parameter or
local in the resulting frame, even after argument writes.

`checked_first_read_error` starts from a normalized module whose first
command reads a declared global. Its exact result is the uninitialized
error with the caller frame restored and the entry heap retained. The
rest of the commands do not run. The executable fixtures also reach
this error inside a closure call and distinguish it from missing and
surplus argument errors before body entry.

The module entry bridge takes evaluated positional actuals. The source
site and operand theorems below supply these premises in a bounded
profile.
[Binding judgments](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Entry/Defs.lean) · [Entry theorems](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Entry/Thms.lean) · [Lean fixtures](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Entry/Checks.lean)

### Root definition sites and call operands

`checked_root_site` relates a normalized root definition at its source
command position to the ID in the emitted command and the corresponding
entry in the final declaration table. A linked table and earlier
commands can determine the starting offset. Children are appended
before their parent. The admitted suffix can contain name assignments,
expression statements, and unrelated required-parameter definitions in
the forwarding chain profile. Successful suffix compilation preserves
the root entry at the ID its command emitted. The root and other
admitted definitions use the existing chain acceptance evidence,
uniform in their incoming table. The setup theorem gives the root
definition step in the fresh module frame.

The independent operand judgment covers declared global reads, integer
and string literals, and subscript reads. Its list judgment evaluates
the callee first and positional actuals left to right. These operands
retain the frame and heap. A reached callee, receiver, or argument error
prevents later evaluation and dispatch. The source-site theorem places
the corresponding call at its checked expression-statement position.
After successful reads, the independent binder derives each assigned
parameter or an arity failure. The invocation theorem connects this to
the exact resolved activation, and transports a supplied callee-body
execution through caller restoration and the existing denotation via
`exec_iff_denoteBody`.

Intervening successful name assignments with admitted operands can
copy the live closure to another binding. Their emitted commands
occupy the corresponding source segment. Distinct owned module slots
and binding-only writes preserve the original callee and function heap
cell. These theorems leave whole-module sequencing and independent
wrapper/leaf body execution through escape and publication open.
Assignments to the callee binding, effectful or nested-call operands,
defaults, other argument forms, loads, and broader bodies are outside
this proof. The Lean fixtures distinguish operand failures from
surplus arity and exercise linked code, later unrelated definitions,
and a copy of the live closure.
[Judgments](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/RootCall/Defs.lean) · [Theorems](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/RootCall/Thms.lean) · [Lean fixtures](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/RootCall/Checks.lean) · [Pinned call semantics](https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#function-calls)

### Wrapper returns and reached command prefixes

The compiler now records the child ID used inside every wrapper.
Checked module elaboration preserves the entire emitted chain in the
final declaration table, including through admitted unrelated suffix
definitions. If the root definition is the first command, fresh module
entry supplies its target cell and the addresses it captures.

A wrapper here has a required positional signature and a body consisting
of its child's definition followed by a return of the child's lexical
name. The independent return rule allocates the child closure and
specifies its address, selected captures, and restored caller state.
The checked activation supplies the local definition cell. The parent
captures and frame layout supply every capture address for the child,
including forwarded local addresses. The proof derives the exact
definition and return body steps, and proves the child cell is
still available after restoration. Pre-existing heap cells and caller
slots are preserved. An assignment of the return to a valid owned
destination reads back the escaped address.

The inductive wrapper path composes successive invocations of escaped
closures. Its bound is the number of available wrapper positions in
the chain. Arity failure stops at the reached invocation with all
earlier allocations retained. Each call body runs with its declaration
removed from the available set. Each separately reached invocation
starts with the full set. The resolved operational path and the
existing dispatch and body denotations agree on the exact result and
state. The path takes already evaluated positional values. The
checked named-assignment theorem uses independent source operand
evidence and derives binding and the wrapper body at the actual
command site. A reached operand or arity error skips the assignment.

The reached-prefix judgment composes source steps in order. Its
transfer theorem preserves the final state at a reached error and passes
a complete trace through the checked publication boundary.
[Wrapper judgments](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Wrapper/Defs.lean) · [Theorems](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Wrapper/Thms.lean) · [Lean fixtures](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Wrapper/Checks.lean)

### Mixed leaf execution and publication

The independent leaf judgment covers the normalized function body
`name, receiver[index] = rhs` followed by `return value`, with one
identifier read in each operand position. It derives lexical references
from the block's owned, enclosing, and module names. Execution reads the
RHS once, checks the two-item unpack before either write, sets the
local, then reads the receiver and index in the updated frame. The
subscript store and final read share the same heap. A reached error
keeps the earlier writes. The proof identifies the emitted leaf code
and shows that removing compiler scratch bindings gives the exact
frame and heap prescribed by the source rules.

`checked_first_definition` supplies the initial source definition step
and links its declaration chain from checked module entry.
`checked_module` composes definition, setup assignment, and named
positional call steps through escaped wrappers and the mixed leaf.
Call operands use the bounded read-only profile. A reached operand
error skips binding and dispatch. A binding error skips activation.
The theorem takes an independent reached trace with command-site,
live-closure, and lexical evidence. It derives the resolved body
execution and the denotation for both outcomes. Independent
publication collects initialized declared globals in order, exports
public names, and freezes the heap reachable from all collected
values. A reached error restores the caller with the residual heap
and yields no publication. The next theorem constructs this trace
for a stated subset of checked modules.

The Lean fixtures check the exact success exports, freezing, and a
late uninitialized read that preserves a mutation before failure.
A separate fixture derives that late leaf error from the independent
assignment rules. Pinned Go checks escaped mutation, later owner
rebinding in a wider wrapper, and successful publication freezing.
Go's `Program.Init` exposes a mutable partial namespace on failure.
`ExecFileOptions` also exposes that namespace and freezes it. The
checked Lean failure result contains the restored caller and the
retained heap.
[Source judgments](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Leaf/Defs.lean) · [Theorems](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Leaf/Thms.lean) · [Lean fixtures](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Leaf/Checks.lean) · [Pinned Go fixture](../../scripts/starlark/mixed-leaf.go)

### Constructing the bounded module trace

`Trace.checked_source_module` takes a static `Profile` over normalized
commands and successful checked compilation. It derives declaration
collection, lexical evidence, each reached command position and each live
closure cell, starting from the actual module entry. The initial caller
and linked table can be supplied by the host. Module entry allocates
fresh globals, including those in a suffix that may be skipped.

The profile has one leading definition with any finite number of
required-positional define-and-return wrappers. Each reached wrapper
call stores its child in a module name. Each next call names that
result directly. Setup assignments can occur between the calls and
after the leaf call. While a closure is pending, setup must write a
different name. The operands admit integer and string literals,
declared module reads, and recursive subscripts. Setup also admits
list and tuple displays over those operands. The mixed leaf
uses identifier reads in all operand positions. Its local declarations
and nearest capture owners follow the existing checked block layout.
The ordinary validator still rejects invalid emitted signatures and
duplicate module names.

The proof constructs the trace by induction on the source schedule.
It uses independent operand evaluation, argument binding, wrapper
allocation and leaf rules. No execution premise about the reached
commands is needed. An operand error precedes binding, and an arity
error skips activation. At the first error, the trace stops with the
heap from the reached step, including any earlier leaf writes. The
publication rules derive the exact ordered exports, freezing from all
initialized globals including private ones, or caller restoration with
the retained heap and no published mapping.

The fixtures instantiate the theorem from the static profile for
success and two error cases. The corresponding evaluator checks cover
a frozen private tuple, an uninitialized read after a shared write,
and an index error before surplus-argument rejection. The live-binding
theorem below extends this schedule to independent definitions and calls.
[Profile](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Defs.lean) · [Theorems](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Thms.lean) · [Lean fixtures](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Checks.lean)

### Traces with multiple live callees

`Trace.Bindings.checked_module` derives a reached trace for checked
load-free modules that interleave unrelated definitions, setup, and
independent or repeated calls to the same supported bodies. Its source
schedule tracks which definition or escaped child may be called through
each module name. Explicit copies of tracked names can create aliases.
The initial tracked environment is empty. Execution supplies the actual
binding cells, closure addresses, capture lists, and lexical blocks.

For a reached definition, the checked-site theorem locates its actual
declaration index in the final table. Later emissions preserve earlier
indices. On a successful call, a wrapper advances the destination to
its child while keeping other tracked names callable. An explicit copy
uses the closure already held in the source cell. Other assignments
update or remove provenance at their own destination. Each call reads
the live value and uses the shared heap. Successful leaf stores can
change list or dictionary contents while preserving earlier binding
and function cells. The trace stops at the first error and retains
its state. Publication freezes exactly the values reachable from the
initialized globals on success. Failure restores the caller with the
residual heap and no published mapping.

The normal validator still rejects duplicate module bindings. The
profile preserves lexical reads of later-initialized globals, local
assignment before a target read, and mutations through shared aliases.
A callee needs provenance from a definition, a wrapper return, or a direct
name copy. Calls through arbitrary results or collection lookups,
wider bodies and operands, defaults, loads, and text parsing remain
outside this theorem.

The fixtures check a wrapper's escaped child and an unrelated mixed
leaf at distinct table IDs. Both touch the same list. A repeated call
uses an alias to the escaped child. The failure control reaches an
uninitialized read after the second definition mutates the list and
skips the remaining call. The Go control observes the residual state
through `Program.Init`.
[Profile and invariant](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Bindings/Defs.lean) · [Theorems](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Bindings/Thms.lean) · [Lean fixtures](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Bindings/Checks.lean) · [Pinned Go comparison](../../scripts/starlark/multi-callee/check.go)

### Checked positional defaults

`Trace.Defaults.checked_module` constructs an independent reached trace
for one module definition surrounded by read-only or allocation-only
setup assignments. The signature has a required positional prefix and
an optional positional suffix. Default expressions use the module's
defining scope and admit the existing read-only operands and flat list
and tuple displays over those operands. The function body returns one
of its own parameters. Compilation identifies the definition's actual
index in the final declaration table.

The source rules evaluate defaults once in declaration order. Each
operand sees the heap left by its predecessor. A reached error skips
later defaults and leaves the definition target untouched. The module
theorem agrees with operational initialization and the module denotation
on the whole observation, including the restored caller and retained
heap on failure. Successful publication freezes values reachable
through saved defaults even if those values have no exported name.

`checked_installed_defaults` connects successful source evaluation to
the new closure cell. At any later state retaining that cell's closure
record at its address, the independent binder agrees with native call
preparation on the exact activation or an error with the same state.
Explicit operands replace the corresponding defaults, omitted slots
consume the saved values, and missing required slots or surplus
arguments fail before any frame allocation. The finite declaration
guard is the checked module entry table's full index range. Binding
uses the saved values even if the original names have been rebound.
A mutable saved value retains its heap address and observes subsequent
writes through aliases.

The definition-only theorem also has controls for a reached
definition-time error. Go's comparison observes its returned globals
and errors. The Lean fixtures check the residual allocation and its
freeze bit directly.
[Profile and source rules](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Defaults/Defs.lean) · [Theorems](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Defaults/Thms.lean) · [Lean fixtures](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Defaults/Checks.lean) · [Pinned spec][default-parameters] · [Pinned Go comparison](../../scripts/starlark/positional-defaults/check.go)

#### Defaulted calls in the multiple-callee trace

`Trace.Bindings.WithDefaults.checked_module` extends the multiple-callee
schedule with module definitions whose bodies return one of their own
parameters. A reached definition evaluates its defaults before binding
the new closure. Its live evidence connects the stored address, the
emitted declaration in the final table, and the ordered saved values.
An explicit name copy keeps that same address and saved record. Calls
to independent required-argument wrappers and mixed leaves preserve
existing closure cells even when they change a collection that a saved
value aliases.

A defaulted call reads the live callee first and evaluates its bounded
read-only operands left to right. Failed operands stop the call before
binding. Once operands succeed, the independent positional binder uses
the saved record for omitted arguments or reports missing or surplus
arguments before allocating a frame. A successful binding supplies the
activation in which the body reads its parameter. The return restores
the caller, and only a successful return writes the destination.
Starting at actual module entry, the reached source trace agrees with
operational initialization and the module denotation on exact exports
and reachable freezing, or the first error with the residual heap and
no publication.

The shared-profile fixtures interleave an aliased defaulted closure
with a separately called mixed leaf that mutates a saved list. They
check repeated omitted calls, an explicit override, and a reached index
error that precedes both a later uninitialized operand and surplus
arity. The pinned Go control also exercises repeated calls after
rebinding a defining local in a nested function. The checked source
trace covers module-level defaulted definitions and the bounded
escaping wrapper below. Broader nested definitions, defaulted bodies
and operands, computed callable provenance, keywords and spreads,
loads and text parsing remain outside the theorem. The existing rejection of
duplicate module bindings also applies.
[Profile and source rules](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Bindings/Defaults/Defs.lean) · [Theorems](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Bindings/Defaults/Thms.lean) · [Lean fixtures](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Bindings/Defaults/Checks.lean) · [Pinned Go comparison](../../scripts/starlark/default-call-trace/check.go)

#### Escaping nested defaults

The checked schedule also admits a wrapper with one required parameter.
The wrapper defines a positional function whose body returns one of its
own parameters, rebinds the wrapper parameter to an integer, and returns
the child. Defaults may read the wrapper parameter, index that value
with a literal integer, or use an integer or singleton integer list
display. The child body has no captures in this profile.

The source compiler links both declarations at their actual indices.
On entry the wrapper owns a cell initialized by positional binding and
a different cell for the unbound child name. Source defaults evaluate
in that reached frame and run in declaration order. Allocations extend
the heap. On success the child saves the resulting values, including
any mutable alias, before the wrapper write. Returning the child
restores the caller with the same closure cell. The module schedule
tracks its address across copies and uses its saved values for omitted
arguments. An explicit operand overrides its own slot. Publication
freezes values reachable through the saved record.

The failure control allocates the first default before the second
fails on an index. The earlier allocation remains in the residual
heap. The child name stays unbound, the local write and subsequent
module commands are skipped, and there is no publication. Pinned
Starlark-Go agrees on the results and reached error. The Lean checks
also inspect the exact residual heap and restored caller. More general
wrapper bodies, nested chains of defaulted declarations, and captures
in a defaulted child body need separate source rules.
[Profile and source rules](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Defaults/Escape/Defs.lean) · [Frame and body theorems](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Defaults/Escape/Thms.lean) · [Module theorem](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Bindings/Defaults/Thms.lean) · [Lean fixtures](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Defaults/Escape/Checks.lean) · [Pinned Go comparison](../../scripts/starlark/escaping-defaults/check.go)

#### Compositional bodies for defaulted calls

The multiple-callee schedule can also admit a module definition with
a sequence of lexical name assignments followed by a return. The
independent body judgment relates each source operand to its scoped
read and records the reads in source order. The local binder judgment
collects the whole body before any read is resolved. Capture selection
is derived from those reads. The supported operands are name reads,
integers, subscript reads, and singleton list displays over admitted
operands. All assignment targets use owned slots.

`Defaults.Body.body_agrees` derives a complete reached body from that
static relation and the activation invariant. Owned names, including
unbound locals, have fresh binding cells. A selected capture denotes
a live caller cell below the activation's allocation boundary. Each
assignment evaluates its RHS before writing, and any reached error
stops the sequence. The final frame and retained cells agree exactly
with independent operational execution and the body denotation.

Module entry derives the capture addresses and saved-default binding
for root definitions. An alias keeps both records. The source module
trace restores the caller and agrees on publication and freezing or
the first error and residual heap. The fixtures read a module binding
initialized after function definition and compare omitted with explicit
arguments. Calling before that binding initializes retains a prior
local list allocation and assignment, skips subsequent body and
module commands, and leaves the call destination unbound. The pinned
Go control observes its partial globals and error. The Lean control
also checks the residual heap and restored frame.

The generic body theorem accepts live enclosing captures through its
frame premise. The checked module integration derives this premise
for captures of module bindings and for the nested case below.
Control flow and wider body operands and assignment targets remain
outside the compositional body profile.
[Body rules and frame invariant](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Defaults/Body/Defs.lean) · [Theorems](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Defaults/Body/Thms.lean) · [Lean fixtures](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Defaults/Body/Checks.lean) · [Pinned Go comparison](../../scripts/starlark/defaulted-body/check.go)

## Enclosing captures in defaulted bodies

The multiple-callee trace admits an escaping wrapper with required
positional parameters and a compositional child body. The independent
lexical read and binder judgments select the child's free references.
The child can capture any subset of the wrapper's parameters.
`Defaults.Escape.Scoped.checked_site` identifies the emitted declaration
and its ordered capture list at the final table index.

`activate_installs` derives the vector by visiting the declaration's
free references in order and looking up their owned slots in the
reached wrapper activation. `capture_order` proves that the installed
bindings match that order and have no duplicates, so repeated source
reads use the same child slot. Defaults still evaluate in the reached
wrapper frame. The wrapper installs the child, rebinds its first
parameter, and restores the caller. `returned_frame` relates the escaped
closure's record, including both saved values and live cells, to the
compositional child frame. The module theorem carries that record
through aliases and later calls and gives exact operational and
denotational agreement on publication and freezing or the first
reached error with the retained heap and restored caller.

The two-capture fixture reads the second parameter first and reads it
again after reading the first parameter. The first parameter holds a
list at definition time and is rebound to an integer before escape.
Two wrapper activations have different second-parameter values and
disjoint capture cells. Lean checks the exact ordered addresses,
deduplication, saved values, and residual cells on a failed override.
The pinned Go control compares returned values, visible failure state,
and publication freezing. The private capture vector and the failed
child's local allocations are checked in Lean.

Additional enclosing levels, capture of the child-name or module slots
in this wrapper profile, wider bodies, untracked callable provenance,
keywords and spreads, loads, and text parsing remain outside this
integration.
[Source rules](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Defaults/Escape/Scoped/Defs.lean) · [Capture and frame theorems](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Defaults/Escape/Scoped/Thms.lean) · [Lean controls](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Defaults/Escape/Scoped/Checks.lean) · [Pinned Go comparison](../../scripts/starlark/nested-default-body/check.go)

## Finite-manifest loader

`Loader.load` takes a known module ID and an optional session. A session
keeps the shared runtime and the cache for one fixed manifest and linked
declaration table. Manifest array indices are canonical IDs. Each entry
provides its own label table, queried when that module executes a load.
Distinct labels that resolve to the same ID share one successful
initialization and the published values retain their heap identities.
The table uses the first matching label when entries repeat.
The linked declaration table is supplied up front and its signatures and
bodies are checked by the shared module validator. Each source's own
commands, allocations and publication are processed on demand.
[Loader definitions](../../Silmaril/Languages/Starlark/Modules/Loader/Defs.lean)

- A missing label reports the requester and label. An ID outside the
  manifest reports an unknown module when it is requested.
- A cycle reports the current path from the root through the repeated
  ID. The path is local to the request and is discarded when it ends.
- Validation and runtime errors carry the ID of the failing module.
  A missing export is a failure of the importing command. Failure stops
  the remaining commands and propagates to every waiting importer.
- Failed modules leave no cache entry and perform no publication freeze.
  Prior heap effects and successfully published dependencies survive,
  so a later request can retry the failure and reuse those dependencies.
  Callers recover their lexical and iterator state at each module exit.

`runs_iff_denote` proves exact agreement with independent rules on the
result, error, heap and cache. Descent counts inactive manifest IDs and
pending commands, so the loader needs no fuel. A fresh Starlark thread
and publication freeze use the same primitives as `initializeModule`.
Canonical resolution, successful-publication caching and cycle rejection
are policies of this host model. Filesystem I/O, concurrency, custom host
thread state, failure caching and backtraces remain open.
[Theorem header](../../Silmaril/Languages/Starlark/Modules/Loader/Thms.lean) · [Load statements][loading] · [Module execution][modules]

The Go loader fixture supplies the same host policy through `Thread.Load`.
It uses `Program.Init` and freezes globals only on success. This lets it
compare dependency order, aliases and failure effects in the pinned
engine. The cycle and cache policy come from the fixture's host, and the
Go convenience wrapper freezes a partial mapping even on failure.
[Lean loader fixtures](../../Silmaril/Languages/Starlark/Modules/Loader/Checks.lean) · [Go loader fixtures](../../examples/starlark/loader/check.go)

The Lean fixtures cover cross-module captures, private freezing, file-local
aliases, validation, missing exports and failure restoration. The native
fixtures check source order, skipped branches, absent assignment after an
effectful error, and the freeze of exported aliases, their nested values and
reachable function defaults. The pinned Go fixtures compare successful
publication through `ExecFileOptions` and observe failure effects through
`Program.Init`. Go's convenience wrapper also freezes the partial global
mapping on error. The Lean failure and loader fixtures check the shared
heap and absence of publication on failure under the pinned prose policy.
[Lean fixtures](../../Silmaril/Languages/Starlark/Modules/Checks.lean) · [Native fixtures](../../Silmaril/Languages/Starlark/Modules/ExpressionChecks.lean) · [Go fixtures](../../examples/starlark/modules/check.go) · [Pinned starlark-go][go]

```sh
lake build --wfail +Silmaril.Languages.Starlark.Modules.Checks \
  +Silmaril.Languages.Starlark.Modules.ExpressionChecks \
  +Silmaril.Languages.Starlark.Modules.Loader.Checks \
  +Silmaril.Languages.Starlark.Modules.Resolve.Checks \
  +Silmaril.Languages.Starlark.Modules.Resolve.LoopChecks \
  +Silmaril.Languages.Starlark.Modules.Resolve.Capture.Leaf.Checks \
  +Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Checks \
  +Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.Checks \
  +Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Checks \
  +Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.Defaults.Checks \
  +Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Checks \
  +Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Checks \
  +Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped.Checks
```

Use Go 1.25 or newer and run from the repository root.

```sh
fixtures="$(pwd)/examples/starlark"
mixed_leaf="$(pwd)/scripts/starlark/mixed-leaf.go"
multi_callee="$(pwd)/scripts/starlark/multi-callee/check.go"
defaults="$(pwd)/scripts/starlark/positional-defaults/check.go"
default_trace="$(pwd)/scripts/starlark/default-call-trace/check.go"
escaping_defaults="$(pwd)/scripts/starlark/escaping-defaults/check.go"
defaulted_body="$(pwd)/scripts/starlark/defaulted-body/check.go"
nested_default_body="$(pwd)/scripts/starlark/nested-default-body/check.go"
oracle="$(mktemp -d)"
git clone https://github.com/google/starlark-go.git "$oracle"
git -C "$oracle" checkout --detach 4f4267fb140d1e8b91c9bce55cee2f809e8840dd
(cd "$oracle" && go run "$fixtures/modules/check.go" && go run "$fixtures/loader/check.go" &&
  go run "$fixtures/scope/check.go" && go run "$mixed_leaf" && go run "$multi_callee" &&
  go run "$defaults" && go run "$default_trace" && go run "$escaping_defaults" &&
  go run "$defaulted_body" && go run "$nested_default_body")
```

[default-parameters]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#functions
[modules]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#module-execution
[loading]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#load-statements
[expressions]: starlark-functions.md#direct-denotation-of-resolved-expressions
[source-expressions]: starlark-functions.md#resolving-a-normalized-expression
[subscript-assignment]: starlark-functions.md#simple-subscript-assignment
[pattern-assignment]: starlark-functions.md#standalone-pattern-assignment
[augmented-subscript]: starlark-functions.md#integer-augmented-subscript-assignment
[names]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#name-binding-and-variables
[loops]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#for-statements
[go]: https://github.com/google/starlark-go/tree/4f4267fb140d1e8b91c9bce55cee2f809e8840dd
