# Operational transition institutions

A signature fixes a type of states and a type of labels. A sentence `(s, a, t)`
says that a model permits that step. A model is a predicate on such edges,
with the discrete category of models. For a signature map `f : A ⟶ B`, the
sentence translation maps both states and the label forwards. The model
reduct is predicate precomposition. Thus `M (mapEdge f e) ↔ reduct f M e`,
the satisfaction condition checked by the existing atomic institution.
[Institution framework](../../Silmaril/Logic/Institution/Basic.lean) ·
[Operational signatures](../../Silmaril/Logic/Operational/Defs.lean)

## Categories of transitions and machine shapes

The signature categories have identity maps on each carrier and pointwise
composition. `System F`, for a configuration signature functor `F`, bundles
a shape and a relation. A system arrow supplies a shape arrow and proves that
every source step maps to a target step. These arrows compose by chaining the
preservation proofs. `System.Hom.runs` preserves finite labelled runs in
execution order using CSLib's `LTS.MTr`. The same LTS works with the repository's
operational execution API. [Run theorem](../../Silmaril/Logic/Operational/Thms.lean) ·
[Execution and enumeration](../../Silmaril/Semantics/Operational/Execution.lean)

| Shape | Configuration and map |
| --- | --- |
| General | Any state carrier and label carrier, with functions on both. |
| Register machine | Control, a total register file, and a partial byte map. A target register or address selects a source coordinate. Control, words, bytes, and labels map forwards. Byte translation preserves absence. |
| Stack machine | Control and a list of values, with the top first. The list maps pointwise in place and keeps its length. |
| Wasm-style | Store, active frame, and an ordered list of administrative terms. Values can occur in that list. Control is the store/frame pair in the stack presentation. |

Each shape functor composes with the operational institution. A shape map can
change observations or identify states. Moving an actual execution requires
the forward simulation proof. Reflection, termination, and demonic correctness
have separate obligations. [Machine shapes and laws](../../Silmaril/Logic/Operational/Machines/Thms.lean)

The earlier finite-machine institution covers registered finite machine
documents and their properties. The Cambridge Optimising Compilers transition
institution uses steps as models of program theories over injective register
renamings. The institutions here use predicates on steps as models and make
individual permitted transitions the sentences. [Finite machines](automata.md) ·
[Cambridge transition institution](../../Silmaril/Courses/Cambridge/OptimisingCompilers/Institutions/Transitions.lean)

## Checked model connections

- **x86.** The adapter represents a live `RelIsa` state canonically, with
  general-purpose registers and raw backing bytes visible in the shape.
  Its control carrier retains the complete source state, including permissions
  and extension fields. The going and stop equivalences recover the existing
  relation on live sources. A stop goes to an explicit stopped configuration
  with no outgoing step. [x86 adapter](../../Silmaril/X86/OperationalInstitution/Thms.lean)
- **WebAssembly Core.** Conversion in both directions preserves the complete
  store, frame, and administrative terms. The adapter reads the existing
  `Core.Step P host` relation verbatim. Its single label is unit, with
  the numeric profile and host relation kept as parameters. The regression
  exercises the Core `nop` rule. [Wasm adapter](../../Silmaril/Wasm/Institution/Operational/Thms.lean)
- **RISC-V.** The public tree has the register-only basic model, the extended
  RV64 machine and its process connection, and the LPS machine. The LPS
  adapter uses `stepAccesses` for a fixed segment list, retaining the complete
  state, integer registers, and overlay-first byte observation. Successful
  edges carry the reported access ranges. A misaligned fetch can yield `fault`
  and an executable image hole can yield `unmodeled`; both names are preserved
  and reach a terminal configuration. The byte observation does not grant
  permission to load. An extended-machine adapter would need a terminal
  encoding for the outcomes of `MState.step`, including instruction and address
  payloads. A process-level LPS adapter would need changing segments and
  syscall transitions. [Basic RV64](../../Silmaril/Machine/RiscV/Basic/Defs.lean) ·
  [Extended machine](../../Silmaril/Machine/RiscV/Ext/Machine/Defs.lean) ·
  [LPS machine](../../Silmaril/RiscV/LPS/Machine.lean) ·
  [LPS adapter](../../Silmaril/RiscV/OperationalInstitution/LPS/Thms.lean)
- **Further connections.** Component linking, kernel-evaluator bridges, other
  ISAs, and architecture-specific operational refinements can supply their own
  shape and step-preservation proofs. The repository's program-level operational
  API records initial states, observations, and UB, which gives a separate seam
  for richer behavioural claims. [Program-level operational API](../../Silmaril/Semantics/Operational/Program/Defs.lean)

## Cambridge L1 and L2

Each adapter uses the course's existing CSLib `lts` as a model of
`Signature.institution`. A sentence `(s, (), t)` names one reduction between
complete configurations. Both endpoints include the expression and a finite
partial store from locations to unbounded integers. `sat_iff` identifies truth
with the course's `Step`, which is call-by-value in L2. The labels carry no
event payload. All configurations are admitted as states, including untyped
and stuck configurations. Converting the model back to a CSLib LTS recovers
the original system, so labelled finite runs keep the same endpoints and one
unit label per step. [Course adapters](../../Silmaril/Courses/Cambridge/OperationalInstitution.lean)

A signature map translates the two endpoints and the label. The reduct tests
the translated edge in the course's LTS. For example, a map that pairs each L1
expression with a fixed store pulls back exactly the reductions that leave
that store unchanged. A simulation between actual systems would also require
step preservation. [Reduct and LTS correspondence](../../Silmaril/Courses/Cambridge/OperationalInstitution/Basic.lean)

The accompanying `OpSem` view reports a finite return exactly when zero or
more course steps reach a value. The return includes the value expression
and its final store, including lambda expressions in L2. Stuck nonvalues
have no return and the view supplies no trap outcomes. The step institution
has individual edge sentences. Return, reachability and terminality are read
from the semantics, and this adapter supplies no sentences for those
properties, divergence, or typing. [L1 return correspondence](../../Silmaril/Courses/Cambridge/L1/OperationalInstitution.lean) ·
[L2 return correspondence](../../Silmaril/Courses/Cambridge/L2/OperationalInstitution.lean)

`ofLTS` packages a CSLib transition system, and `valueSemantics` accepts a
course-specific value predicate for unit-labelled systems. The L1 denotational
adapters use this finite-return view to prove satisfaction of value-and-store
atoms, with the read-only model as a reduct of the effectful model.
The Cambridge step specification format names complete configurations by
bounded catalogue slots and translates conjunctions of step claims into
this institution with a checked satisfaction condition.
[Step specification format](../courses/cambridge-step-specification.md) · [Shared entry points](../../Silmaril/Courses/Cambridge/OperationalInstitution/Basic.lean) ·
[L1 denotations](../courses/cambridge-denotational.md#effectful-l1)

## Cambridge L3

The CSLib wrapper uses the direct L3 `Step` relation verbatim. Each state is
the original `L3.Config` with its expression and a finite partial store of
L3 values. Locations are concrete natural numbers. Every fresh location gives
its own permitted allocation edge, and the model keeps the inserted binding
in the target store. `sat_iff` identifies satisfaction with the direct rules,
and `steps_iff_reachable` identifies finite CSLib reachability with `L3.Steps`.
[L3 adapter](../../Silmaril/Courses/Cambridge/L3/OperationalInstitution.lean)

The sentence logic consists of atomic positive edge claims `(s, (), t)` with
one unit label per step. A return is a separate `OpSem.May` observation. It
witnesses a finite run to an `L3.IsValue` expression and reports that expression
with the full final store. Concrete fresh names remain visible, even when two
runs return the same expression. The view supplies no trap outcomes. Must
observations, divergence, and equivalence up to location renaming require
separate proof obligations. [Finite return correspondence](../../Silmaril/Courses/Cambridge/L3/OperationalInstitution.lean)

## Checks

Run the three module builds and the regression with the pinned toolchain.

```sh
lake build --wfail +Silmaril.Logic.Operational.Machines.Thms \
  +Silmaril.X86.OperationalInstitution.Thms +Silmaril.Wasm.Institution.Operational.Thms
lake env lean -DwarningAsError=true tests/semantics/operational-institutions/Regression.lean
```

The regression checks the composition of simulations on finite runs, register
and memory-map variance, satisfaction under translation, stack order, and the
Wasm and x86 adapters.

The Cambridge build checks L1 assignment, dereference at a fixed store,
and a missing location. It also checks an L2 run that dereferences the
argument before beta reduction and returns the value with the final store.
The L3 examples rule out allocating at an occupied location and check two
runs of `!(ref 42)` that reach the same integer with distinct final stores.
[L1 and L2 examples](../../Silmaril/Courses/Cambridge/OperationalInstitution/Examples.lean) ·
[L3 examples](../../Silmaril/Courses/Cambridge/OperationalInstitution/L3Examples.lean)

```sh
make check CHECK_TARGETS='+Silmaril.Courses.Cambridge.OperationalInstitution'
```

The RV64 regression runs real instruction bytes through the landed model.
`LD` returns the overlaid value `43` and reports eight bytes at address `256`.
`LB` and `LBU` each report one byte at that address. For input `0x80`, they
produce respectively `0xffffffffffffff80` and `0x0000000000000080` in `a0`.
These are concrete width cases. The shared register observation projects
x86 RAX and RV64 a0 independently. The tagged x86/Wasm test proves that a
finite run in the tagged aggregate keeps its initial origin in every label
and its endpoint. The individual x86 and Wasm relations remain parameters of
that aggregate. [RV64 and tag regression](../../tests/semantics/rv64-operational/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.RiscV.OperationalInstitution.LPS.Thms'
```
