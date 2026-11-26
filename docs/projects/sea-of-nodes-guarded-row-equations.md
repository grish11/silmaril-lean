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
import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Institution.Thms
import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Fuel.Thms

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (model word)
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing (WordTuple words)
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA (inputEnv)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA

def exitRow : Spec :=
  ⟨[0, 1], [0, 1], [⟨.add, 0, 0, 1⟩], .output 0 0, 0, .ne, 3, 0⟩

def spinRow : Spec :=
  { exitRow with entry := [0, 0], updates := [⟨.add, 0, 0, 1⟩, ⟨.sub, 1, 1, 1⟩] }

def sample (spec : Spec) (backedges : Nat) := do
  let p ← checkPlan 2 spec
  let (rtl, ssa) ← lowerChecked 2 spec
  let input : WordTuple 2 := .cons (0 : Word) (.cons (1 : Word) .nil)
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
```

At input `(0, 1)` both terms exhaust a one-backedge budget. The exit
row takes two backedges, then compares the newly computed 3 and
returns the old slot value 2. The spin row starts at `(0, 0)`.
That tuple is an invariant that forces another backedge and excludes
every finite return. The native equation therefore fails at this
valuation, and `equation_at_iff` carries the distinction to the
emitted targets. [Checked regression][regression]

```sh
lake build --wfail +Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Institution.Regression
```

[native]: sea-of-nodes/control-flow/sea-of-nodes-loop-institution.md
[fuel]: https://github.com/hiloopai/silmaril-lean/pull/3779
[thms]: ../../Silmaril/Machine/SeaOfNodes/Loop/RTL/Routing/Guarded/Rows/Institution/Thms.lean
[occurrences]: ../../Silmaril/Machine/SeaOfNodes/Loop/RTL/Routing/Guarded/Rows/Thms.lean
[regression]: ../../Silmaril/Proofs/Machine/SeaOfNodes/Loop/RTL/Routing/Guarded/Rows/Institution/Regression.lean
