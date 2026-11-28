# Native guarded-row loop equations

`Plan.program` packages the checked single-header i64 graph in the existing
native loop institution, preserving the producer table and both incoming
Phi columns. `Plan.equation` pairs two such programs of the same input
width and word result. Pass the `checkPlan` and `lowerChecked` successes to
`equation_at_iff` for one typed input or to `equation_holds_iff` for
all valuations. Both backends consume the same native tuple through the
existing `words` and `inputEnv` encodings. Signature relabelling still
uses the native `Sentence.satisfaction` theorem.
[Native loop institution][native] · [Public API][thms]

The relational observations are sets of finite (word, whole final memory)
returns. On either emitted target the set is empty exactly when the
native partial value is undefined. A returned word is paired with the
entire initial memory. `no_finite_return_iff` quantifies over all RTL
returns and all λSSA evaluations. The same theorem applies to either
predecessor slot order because `incoming_alignment` reads back the
same emitted branches. The scope is the pure computed-guard bank
accepted by `checkPlan`.
[Whole-loop lowering][fuel] · [Occurrence alignment][occurrences]

```lean
import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Reindex.Thms
import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Fuel.Thms
import Mathlib.Logic.Equiv.Basic

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (model word)
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing (WordTuple words)
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA (inputEnv)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA

def exitRow : Spec :=
  ⟨[0, 1], [0, 1], [⟨.add, 0, 0, 1⟩], .output 0 0, 0, .ne, 3, 0, none, none⟩

def spinRow : Spec :=
  { exitRow with entry := [0, 0], updates := [⟨.add, 0, 0, 1⟩, ⟨.sub, 1, 1, 1⟩] }

def sample (spec : Spec) (backedges : Nat)
    (input : WordTuple 2 := .cons (0 : Word) (.cons (1 : Word) .nil)) := do
  let p ← checkPlan 2 spec
  let (rtl, ssa) ← lowerChecked 2 spec
  let initial := Memory.ofList 4 [29, 71, 53, 11]
  let native := p.graph.evalBackedges model backedges input
  let machine := (rtl.runMain (p.rtlFuel backedges) 0 (words input) initial).returnedValues?
  let typed := (Generic.Fuel.run model (inputEnv model input) (backedges + 1) ssa).bind
    fun (_, packet) => (Generic.Fuel.decodeArgs model [word] packet).map fun fields =>
      Silmaril.SSA.RVSDG.Tuple.get fields .head
  pure (native.map BitVec.toNat, machine.map (List.map BitVec.toNat), typed.map BitVec.toNat)

#eval (sample exitRow 1, sample spinRow 1, sample exitRow 2, sample spinRow 2)
-- (some (none, none, none), some (none, none, none),
--  some (some 2, some [2], some 2), some (none, none, none))

#eval
  let perm : InputPermutation 2 := Equiv.swap 0 1
  let onSwappedInput (spec : Spec) (budget : Nat) :=
    sample (spec.reindexInputs perm) budget (.cons (1 : Word) (.cons (0 : Word) .nil))
  (onSwappedInput exitRow 1, onSwappedInput spinRow 1,
    onSwappedInput exitRow 2, onSwappedInput spinRow 2)
-- (some (none, none, none), some (none, none, none),
--  some (some 2, some [2], some 2), some (none, none, none))
```

At input `(0, 1)` both terms exhaust a one-backedge budget. The exit
row takes two backedges, then compares the newly computed 3 and
returns the old slot value 2. The spin row starts at `(0, 0)`.
That tuple is an invariant that forces another backedge and excludes
every finite return. The native equation therefore fails at this
valuation, and `equation_at_iff` carries the distinction to the
emitted targets. [Checked regression][regression]

## Checked dependent preheaders

The native observation sentences also apply to checked dependent-preheader
graphs. `Table.Institution.equation_holds_iff` relates the existing native
equation to equality of the emitted RTL and λSSA finite return sets.
`terminates_holds_iff` uses nonemptiness of those sets at each typed input.
[Bridge and runnable example](sea-of-nodes-guarded-feedback-rows-rtl.md#satisfaction-of-observation-equations)

## Permuting the external input interface

`InputPermutation n` maps each old input slot to its new position.
Call `spec.reindexInputs perm` before `lowerChecked`. Only the preheader's
external reads change. Carried bank indices, producer indices and incoming
occurrences keep their identities. In the new interface, `perm.pull input`
is the corresponding old valuation.

`lowerChecked_reindex` proves that an accepted row rechecks and emits both
targets of the typed map. `denote_mapGraph_reindex` composes that input map
with native opcode relabelling and reduct. The emitted-target theorems use
the concrete word model and compare unbounded finite returns, whole memory,
and undefinedness at the pulled valuation. [Reindexing API][reindex]

For a pair of checked re-emissions, `reindex_equation_at_iff` compares
the left RTL and right λSSA observations at the new input with the
original native equation at `perm.pull input`. The two-row example
above re-emits both specs and retains the distinction at `(1, 0)`.
`reindex_equation_holds_iff` lifts this comparison to all valuations.
`InputPermutation.pull_symm` supplies a new valuation for every old
one. When the native equation is also opcode-relabelled,
`equation_reindex_map_holds_iff` uses `Sentence.satisfaction` to
compare it in the reduct model. [Equation regression][regression]

```lean
import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Reindex.Thms
import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Fuel.Thms
import Mathlib.Logic.Equiv.Basic

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (model word)
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing (WordTuple words)
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA (inputEnv)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA

def row : Spec :=
  ⟨[0, 1], [0, 1], [⟨.add, 0, 0, 1⟩], .output 0 0, 0, .ne, 3, 0, none, none⟩

def swapInputs : InputPermutation 2 := Equiv.swap 0 1
def bank (x y : Word) : WordTuple 2 := .cons x (.cons y .nil)

def observe (spec : Spec) (input : WordTuple 2) := do
  let p ← checkPlan 2 spec
  let (rtl, ssa) ← lowerChecked 2 spec
  let memory := Memory.ofList 4 [29, 71, 53, 11]
  let machine := (rtl.runMain (p.rtlFuel 2) 0 (words input) memory).returnedValues?
  let typed := (Generic.Fuel.run model (inputEnv model input) 3 ssa).bind
    fun (_, packet) => (Generic.Fuel.decodeArgs model [word] packet).map fun fields =>
      Silmaril.SSA.RVSDG.Tuple.get fields .head
  pure (machine.map (List.map BitVec.toNat), typed.map BitVec.toNat)

#eval (observe row (bank 0 1), observe (row.reindexInputs swapInputs) (bank 1 0),
  observe row (bank 1 0))
-- (some (some [2], some 2), some (some [2], some 2), some (none, none))
```

The first two calls latch `(0, 1)` and return old slot 0 after two
backedges. The last call latches `(1, 0)`, a fixed point whose guard
always takes the backedge. The checked example proves this absence of a
finite return and checks both slot presentations of the re-emitted λSSA
header. [Reindexing regression][reindex-regression]

```sh
lake build --wfail \
  +Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Institution.Regression \
  +Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Reindex.Regression
```

[native]: sea-of-nodes/control-flow/sea-of-nodes-loop-institution.md
[fuel]: https://github.com/hiloopai/silmaril-lean/pull/3779
[thms]: ../../Silmaril/Machine/SeaOfNodes/Loop/RTL/Routing/Guarded/Rows/Institution/Thms.lean
[occurrences]: ../../Silmaril/Machine/SeaOfNodes/Loop/RTL/Routing/Guarded/Rows/Thms.lean
[regression]: ../../Silmaril/Proofs/Machine/SeaOfNodes/Loop/RTL/Routing/Guarded/Rows/Institution/Regression.lean
[reindex]: ../../Silmaril/Machine/SeaOfNodes/Loop/RTL/Routing/Guarded/Rows/Reindex/Thms.lean
[reindex-regression]: ../../Silmaril/Proofs/Machine/SeaOfNodes/Loop/RTL/Routing/Guarded/Rows/Reindex/Regression.lean
