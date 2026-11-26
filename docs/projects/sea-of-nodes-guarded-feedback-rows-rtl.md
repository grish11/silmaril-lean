# Guarded feedback rows in RTL and explicit Φ

Import `Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Fuel.Thms`.
`checkPlan` admits a typed i64 bank at a supplied width. Entry and copy
indices are zero-based and checked against the full bank. Each computation
reads two old bank slots and writes a fresh temporary. Destinations are
distinct. The guard names one computed producer and its destination.
The checker requires them to agree. The guard compares that producer
with `eq`, `ne`, or signed `slt` against `limit` by default. Set
`guardRhs := some (.arg slot)` to read an old bank slot, or
`guardRhs := some (.output producer 0)` to read a distinct row result.
Exit reads the old `exitSlot` by default. Set
`exitOrigin := some (.output producer 0)` to return a computed result
from that activation. The checker requires that producer's destination
to be `exitSlot`. Positional `Spec` literals take `exitOrigin` followed
by `guardRhs`.
[Guarded pair][pair] · [Row compiler][row] · [Explicit Φ baseline][phi]

```lean
import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Fuel.Thms

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (model word)
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing (WordTuple words)
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA (inputEnv)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA

def crossed : Spec where
  entry := [0, 1, 2]
  copies := [0, 1, 0]
  updates := [⟨.sub, 1, 0, 1⟩, ⟨.add, 0, 0, 1⟩]
  guardOrigin := .output 1 0
  guardDestination := 0
  comparison := .ne
  limit := 14
  exitSlot := 2

def sampleInput : WordTuple 3 := .cons (5 : Word) (.cons (2 : Word) (.cons (20 : Word) .nil))

#eval do
  let plan ← checkPlan 3 crossed
  let (rtl, ssa) ← lowerChecked 3 crossed
  let mem := Memory.ofList 4 [29, 71, 53, 11]
  let observe (backedges : Nat) :=
    let machine := (rtl.runMain (plan.rtlFuel backedges) 0 (words sampleInput) mem).returnedValues?
    let typed := (Generic.Fuel.run model (inputEnv model sampleInput) (backedges + 1) ssa).bind fun (_, packet) =>
      (Generic.Fuel.decodeArgs model [word] packet).map fun fields => Silmaril.SSA.RVSDG.Tuple.get fields .head
    (machine.map (List.map BitVec.toNat), typed.map BitVec.toNat)
  pure (observe 1, observe 2)
-- some ((none, none), some [7], some 7)
```

The first two activations feed back `(7, 3, 5)` and `(10, 4, 7)`.
The guard's addition reads old slot 1 even though the subtraction
replaces it, and slot 2 copies old slot 0. The next comparison sees 14
and exit projects the old slot 2, which is 7. Changing the guard origin
to `.output 0 0` is refused because producer 0 writes slot 1.
[Activation regression][regression] · [Whole-loop regression][fuel-regression]

`activation_agrees` proves the guard choice and complete feedback tuple
or exit projection. `incoming_alignment` identifies the actual entry
and feedback branches in either predecessor order. The two orders
recover the same branch terms of the emitted CFG. [Activation theorems][thms]

For a row with `k` computations, `activationSteps` is `k + 3`
with a fixed limit and `k + 2` with an old-bank or computed operand.
Both execute the row, comparison and branch. The fixed limit adds one literal.
A return after `b` backedges needs exactly
`activationSteps * (b + 1) + 2` RTL steps including entry and return,
and `b + 1` λSSA visits. The fixed-limit example needs 17 RTL steps
and 3 λSSA visits.
`runMain_fuel_iff` gives the threshold at arbitrary RTL fuel.
`bounded_returns_iff` and `bounded_absence_iff` compare observation at
the matched budgets. `returns_iff` relates the checked targets' finite
returns with the entire final memory equal to the initial memory.
The proofs cover the current pure single-header i64 bank profile.
[Whole-loop theorems][fuel-thms]

## Return a computed row value

A native loop can name a header producer in its result wire, as the
source swap example does. This add/sub row selects the exit producer
independently of the guard producer. The selection uses the existing
exit successor and introduces no additional machine step.
[Native result wire][native-result]

```lean
import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Fuel.Thms

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (model word)
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing (WordTuple words)
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA (inputEnv)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA

def subtractOnExit : Spec where
  entry := [0, 1, 2]
  copies := [0, 1, 2]
  updates := [⟨.add, 0, 0, 1⟩, ⟨.sub, 2, 2, 1⟩]
  guardOrigin := .output 0 0
  guardDestination := 0
  comparison := .ne
  limit := 3
  exitSlot := 2
  exitOrigin := some (.output 1 0)

def observe (spec : Spec) (input : WordTuple 3) := do
  let plan ← checkPlan 3 spec
  let (rtl, ssa) ← lowerChecked 3 spec
  let initial := Memory.ofList 4 [29, 71, 53, 11]
  let machine := (rtl.runMain (plan.rtlFuel 2) 0 (words input) initial).returnedValues?
  let typed := (Generic.Fuel.run model (inputEnv model input) 3 ssa).bind
    fun (_, packet) => (Generic.Fuel.decodeArgs model [word] packet).map fun fields =>
      Silmaril.SSA.RVSDG.Tuple.get fields .head
  pure (machine.map (List.map BitVec.toNat), typed.map BitVec.toNat)

#eval observe subtractOnExit (.cons (0 : Word) (.cons (1 : Word) (.cons (10 : Word) .nil)))
-- some (some [7], some 7)

#eval observe { subtractOnExit with limit := 42, guardRhs := some (.arg 2) }
  (.cons (0 : Word) (.cons (1 : Word) (.cons (5 : Word) .nil)))
-- some (some [2], some 2)

#eval observe { subtractOnExit with guardRhs := some (.output 1 0) }
  (.cons (0 : Word) (.cons (1 : Word) (.cons (6 : Word) .nil)))
-- some (some [3], some 3)

def signedCrossing : Spec :=
  { subtractOnExit with
    updates := [⟨.add, 0, 0, 1⟩, ⟨.add, 2, 2, 1⟩]
    comparison := .slt
    guardRhs := some (.output 1 0) }

#eval observe signedCrossing (.cons (-2 : Word) (.cons (1 : Word) (.cons (0x7fff_ffff_ffff_fffe : Word) .nil)))
-- some (some [9223372036854775808], some 9223372036854775808)
```

At `(0, 1, 10)` two backedges lead to old bank `(2, 1, 8)`.
The exit guard sees 3 and returns the freshly computed `8 - 1 = 7`.
An old-slot exit would return 8. With stride zero and counter 1 a
fixed-point proof excludes every finite return in both targets.
Selecting guard producer 0 as the exit origin while retaining
`exitSlot := 2` is refused. `no_finite_return_iff` in
`Rows.Institution.Thms` applies to either exit selection.
[Computed exit regression][computed-regression] · [Observation laws][institution-thms]

## Compare with an old bank slot

The source swap loop's comparison with a runtime input motivates this
two-operand guard. An old bank slot can supply the right operand of
any supported comparison. In the second call above, two backedges lead
to `(2, 1, 3)`. The guard compares the next counter 3 with old slot 2's
value 3. The subtraction has already computed 2 for that slot, and
the exit passes that computed word. The return takes 14 RTL steps and
3 λSSA visits. The checker rejects an out-of-range `.arg` slot for
`guardRhs`. Reindexing the external inputs leaves that bank-local
operand in place. [Native loop example][native-result] · [Operand regressions][operand-regression]

## Compare two row results

Simple's chapter 13 loop regression has a continuation branch that
compares two arithmetic expressions. The last call above uses the same
operand shape with a single `ne` guard over an add and a subtraction.
Both producers read the old bank. At `(2, 1, 4)` the computed words
are both 3, so the loop exits. Using the old value 4 as the RHS would
take the backedge. `guard_compare_computed` identifies the two actual
RTL producer registers. The regression also inspects the emitted λSSA
operands and branch packets, then checks both returns under an external
input swap. A producer outside the update row, a port other than 0,
and reuse of the left producer are refused. [Simple loop branch][simple-two-expressions] · [Operand regressions][operand-regression]

## Signed less-than

Simple's pinned `BoolNode.LT` compares signed Java `long` operands.
For `comparison := .slt`, RTL emits `cmp lts lhs rhs` and λSSA
interprets the typed `WordOp.slt` in the native word model. In
`signedCrossing`, the first comparison is `-1 < 2^63 - 1` and takes
feedback. The next RHS wraps to `-2^63`, so `0 < -2^63` is false and
the computed RHS is returned. Unsigned order or swapped operands
would exit on the first visit. The regression checks both actual
branch packets, the whole memory, and no finite return for a zero
stride. It also checks re-emission after swapping inputs 0 and 1
using `Rows.Reindex.Thms`.
[Simple comparison class][simple-lt] · [Signed guard regression][signed-regression]

## Check a native signed loop

`Rows.Native.lowerChecked` takes a typed `BankGraph` directly.
It reconstructs the guarded row from the native header and its entry
and feedback columns, then checks the reconstructed opcodes and typed
wire origins against the graph. `Native.recognize_sound` proves the
checked plan reconstructs that graph, including the predicate and
exit projection. `Native.activation_agrees` identifies the taken
packet in both emitted targets. The two return iff laws preserve the
whole memory, and `Native.no_finite_return_iff` handles undefinedness
without choosing a common fuel.

The admitted shape has an empty preheader and equal input and bank widths.
Each wrapping add/sub reads the old bank and supplies exactly one feedback
destination. Remaining feedback slots copy old words. The final signed
comparison takes a computed result on the left and either a distinct row
result or a latched bank slot on the right. The recognizer translates old
header argument positions to bank-local slots. Captured inputs and literal
operands are outside this profile. The true successor feeds back the whole
tuple and the false successor returns an old field or a row result, as
specified by the native `Loop.Graph`.

This example isolates Simple chapter 13's
`(arg + 79) < (32 - arg)` continuation test. The example passes
the offsets as inputs and exposes the computed RHS on exit.
[Simple loop branch][simple-two-expressions] · [Native regression][native-guard-regression]

```lean
import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Thms

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (model word)
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows
open Silmaril.SSA.RVSDG (Origin)
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA (inputEnv)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA

def oldPort (slot : Fin 4) := suffixPort (wordPorts 4) (argumentPort 4 slot)

def source (rhs : Origin (bankArgs 4) [[wordPort], [wordPort]] wordPort) :
    BankGraph 4 [[wordPort], [wordPort], [.value .predicate]] where
  preheader := .nil
  header :=
    .cons .add (.cons (.arg (oldPort 0)) (.cons (.arg (oldPort 1)) .nil))
      (.cons .sub (.cons (.arg (oldPort 2)) (.cons (.arg (oldPort 0)) .nil))
        (.cons .slt (.cons (.output (0 : Fin 2) .head) (.cons rhs .nil)) .nil))
  phiInputs
    | .entry => .cons (.arg (argumentPort 4 0)) (.cons (.arg (argumentPort 4 2))
        (.cons (.arg (argumentPort 4 1)) (.cons (.arg (argumentPort 4 3)) .nil)))
    | .backedge => .cons (.output (0 : Fin 3) .head) (.cons (.arg (oldPort 1))
        (.cons (.arg (oldPort 2)) (.cons (.output (1 : Fin 3) .head) .nil)))
  predicate := .output (2 : Fin 3) .head
  result := .output (1 : Fin 3) .head

def observeNative (rhs : Origin (bankArgs 4) [[wordPort], [wordPort]] wordPort)
    (rtlFuel lambdaFuel : Nat) := do
  let (rtl, ssa) ← Native.lowerChecked (source rhs)
  let input : WordTuple 4 := .cons (-80 : Word) (.cons (32 : Word) (.cons (79 : Word) (.cons (0 : Word) .nil)))
  let mem := Memory.ofList 4 [29, 71, 53, 11]
  let machine := (rtl.runMain rtlFuel 0 (words input) mem).returnedValues?
  let typed := (Generic.Fuel.run model (inputEnv model input) lambdaFuel ssa).bind fun (_, packet) =>
    (Generic.Fuel.decodeArgs model [word] packet).map fun fields => Silmaril.SSA.RVSDG.Tuple.get fields .head
  pure (machine.map (List.map BitVec.toInt), typed.map BitVec.toInt)

#eval observeNative (.output (1 : Fin 2) .head) 10 2
-- some (some [33], some 33)

#eval observeNative (.arg (oldPort 3)) 14 3
-- some (some [-46], some (-46))
```

The first guard compares `-1 < 112` and feeds back
`(-1, 79, 32, 112)`. Both unsigned and reversed comparison would
return 112 there. The next guard compares `78 < 33`, so both targets
return the fresh RHS 33. The checker refuses changing the add's left
operand to the captured input, which would stop reading the latched value.

With the old bank RHS, the second guard compares 78 with the latched 112
and takes another backedge. The fresh RHS 33 would exit at that point.
Both targets return the computed word `-46` on the third visit. Swapping
the operands puts the old slot on the left and is refused. Using the
captured input at absolute header port 3 in place of old slot 3 at port 7
is also refused. [Native regression][native-guard-regression]

## Latch a computed initializer

Import `Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Thms`.
`Native.Preheader.lowerChecked` takes a native graph with one preheader
producer, a wrapping i64 add or sub over captured inputs. At least one
entry slot must read its result. Other entry reads come from the captured
inputs. The header uses the existing signed guarded-row profile with equal
input and bank widths. `Native.lowerChecked` still handles the empty
preheader. The checker for this extension rejects literal initializers.
[Simple's first Loop/Phi arrival][simple-latch]

`recognize_sound` proves exact reconstruction of the typed source.
`entry_packet` relates the RTL initializer and jump to the λSSA entry
packet while preserving captures. `header_packet` relates the taken
feedback tuple or exit word in the emitted targets. Feedback rebinds the
whole bank from the old snapshot. The return and absence iff laws use
native finite execution and preserve the entire initial memory on return.

For a return after `b` backedges, `rtl_runMain_fuel_iff` gives the exact
minimum of `activationSteps * (b + 1) + 3` instructions, including the
initializer, jump, and return. `lambda_run_succ` uses `b + 1` header
visits and evaluates entry outside that budget. The two runners count
different operations. [Checked regressions][preheader-regression]

```lean
import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Thms

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (model word)
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA (inputEnv)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA

def capture (slot : Fin 3) := argumentPort 3 slot
def old (slot : Fin 3) := suffixPort (wordPorts 3) (capture slot)

def initialized : Preheader.Source 3 [[wordPort], [.value .predicate]] where
  preheader := .cons .sub (.cons (.arg (capture 0)) (.cons (.arg (capture 2)) .nil)) .nil
  header :=
    .cons .add (.cons (.arg (old 0)) (.cons (.arg (old 1)) .nil))
      (.cons .slt (.cons (.output (0 : Fin 1) .head) (.cons (.arg (old 2)) .nil)) .nil)
  phiInputs
    | .entry => .cons (.output (0 : Fin 1) .head) (.cons (.arg (capture 1)) (.cons (.arg (capture 2)) .nil))
    | .backedge => .cons (.output (0 : Fin 2) .head) (.cons (.arg (old 1)) (.cons (.arg (old 2)) .nil))
  predicate := .output (1 : Fin 2) .head
  result := .output (0 : Fin 2) .head

#eval do
  let (rtl, ssa) ← Preheader.lowerChecked initialized
  let input : WordTuple 3 := .cons (6 : Word) (.cons (2 : Word) (.cons (5 : Word) .nil))
  let mem := Memory.ofList 4 [29, 71, 53, 11]
  let machine := (rtl.runMain 9 0 (words input) mem).returnedValues?
  let typed := (Generic.Fuel.run model (inputEnv model input) 2 ssa).bind fun (_, packet) =>
    (Generic.Fuel.decodeArgs model [word] packet).map fun fields => Silmaril.SSA.RVSDG.Tuple.get fields .head
  pure (machine.map (List.map BitVec.toInt), typed.map BitVec.toInt)
-- some (some [5], some 5)
```

The initial bank is `(1, 2, 5)`, so the first comparison is `3 < 5`
and feeds back `(3, 2, 5)`. Passing the raw first capture to slot 0
would instead test `8 < 5` and exit on the first visit. A captured read
in a feedback copy is refused even when it currently agrees with the
corresponding bank slot.

## Schedule dependent preheader producers

Import `Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Thms`.
`Table.lowerChecked` admits a typed, straight-line preheader made of
wrapping i64 adds and subs. Each operand can read a captured input or an
earlier result. At least one entry slot must read a computed result.
The checker keeps the original ordered entry column and reuses the
existing signed-row header check. `recognize_sound` recovers the exact
native graph. The original empty and singleton entry APIs are available
for their respective profiles.

`entry_block` proves that the emitted RTL operations preserve the whole
memory and make every native capture and computed word available in its
assigned register. `entry_packet` covers the subsequent simultaneous
bank binding in both RTL.SSA and explicit-Φ λSSA. Feedback and exit use
the existing header proof. The return and absence iff laws relate both
targets to native finite execution, with full memory equality on return.

With `k` producers and `b` backedges the minimum RTL fuel is
`k + activationSteps * (b + 1) + 2` instructions. This includes `k`
preheader operations, one entry jump, and one return. The λSSA runner
evaluates entry outside its budget and needs `b + 1` header visits.
[Checked regression][table-regression]

```lean
import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Reindex.Thms

open Silmaril.Isotope.Institution.Observational (Observation ssaBeh)
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA.Institution.Fiber (inputModel)
open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL.SSA (Behavior)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (model word)
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader
open Silmaril.Machine.SeaOfNodes.Loop.RTL
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded
open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA (inputEnv)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA

def capture (slot : Fin 3) := argumentPort 3 slot
def old (slot : Fin 3) := suffixPort (wordPorts 3) (capture slot)

def dependent :
    SourceWithEntry 3 [[wordPort], [wordPort]] [[wordPort], [.value .predicate]] where
  preheader :=
    .cons .sub (.cons (.arg (capture 0)) (.cons (.arg (capture 2)) .nil))
      (.cons .add (.cons (.output (0 : Fin 1) .head) (.cons (.arg (capture 1)) .nil)) .nil)
  header :=
    .cons .add (.cons (.arg (old 0)) (.cons (.arg (old 1)) .nil))
      (.cons .slt (.cons (.output (0 : Fin 1) .head) (.cons (.arg (old 2)) .nil)) .nil)
  phiInputs
    | .entry =>
      .cons (.output (0 : Fin 2) .head) (.cons (.output (1 : Fin 2) .head) (.cons (.arg (capture 2)) .nil))
    | .backedge =>
      .cons (.output (0 : Fin 2) .head) (.cons (.arg (old 1)) (.cons (.arg (old 2)) .nil))
  predicate := .output (1 : Fin 2) .head
  result := .output (0 : Fin 2) .head

#eval do
  let (rtl, ssa) ← Table.lowerChecked dependent
  let input : WordTuple 3 := .cons (6 : Word) (.cons (2 : Word) (.cons (5 : Word) .nil))
  let mem := Memory.ofList 4 [29, 71, 53, 11]
  let machine := (rtl.runMain 10 0 (words input) mem).returnedValues?
  let typed := (Generic.Fuel.run model (inputEnv model input) 2 ssa).bind fun (_, packet) =>
    (Generic.Fuel.decodeArgs model [word] packet).map fun fields => Silmaril.SSA.RVSDG.Tuple.get fields .head
  pure (machine.map (List.map BitVec.toInt), typed.map BitVec.toInt)
-- some (some [7], some 7)

example {targets : Checked.Phi.Targets} (accepted : Table.lowerChecked dependent = some targets)
    (input : WordTuple 3) (initial : Memory) :
    Table.rtlDenote targets.1 input initial = Table.nativeDenote dependent input initial ∧
      Table.lambdaDenote targets.2 input initial = Table.nativeDenote dependent input initial :=
  Table.denotations_eq accepted input initial

def bank (x y z : Word) : WordTuple 3 := .cons x (.cons y (.cons z .nil))

theorem spinAbsent : dependent.denote model (bank 0 1 1) = Part.none := by
  rw [Part.eq_none_iff', Part.dom_iff_mem]
  rintro ⟨value, present⟩
  exact dependent.not_returns_of_backedge_invariant model (bank 0 1 1) value
    (· = bank (-1) 0 1) (by cbv)
    (fun old fixed => fixed.symm ▸ ⟨bank (-1) 0 1, by cbv, rfl⟩)
    ((dependent.returns_iff_mem_denote model _ _).mpr present)

example {targets : Checked.Phi.Targets} (accepted : Table.lowerChecked dependent = some targets)
    (initial : Memory) :
    ¬ (∀ input : WordTuple 3, (Rows.rtlObservation targets.1 input initial).Nonempty) ∧
    ¬ (∀ input : WordTuple 3,
        (Table.Institution.lambdaReturns input initial (Table.Institution.scope accepted)).Nonempty) := by
  have absent : ¬ (Loop.Institution.Sentence.terminates (Table.Institution.program dependent)).Holds model :=
    fun holds => (Part.eq_none_iff'.mp spinAbsent) (holds (bank 0 1 1))
  have agrees := Table.Institution.terminates_holds_iff accepted initial
  exact ⟨absent ∘ agrees.1.mp, absent ∘ agrees.2.mp⟩

example {targets : Checked.Phi.Targets} (accepted : Table.lowerChecked dependent = some targets)
    (initial : Memory) :
    Observation.diverge initial ∈ ssaBeh 1
      (inputModel (P := Rows.wordSignature) model Memory (bank 0 1 1))
      (Table.Institution.scope accepted) :=
  (Table.Institution.room_diverges_iff accepted (bank 0 1 1) initial).mpr spinAbsent

example {targets : Checked.Phi.Targets} (accepted : Table.lowerChecked dependent = some targets)
    (initial : Memory) :
    targets.1.divOracle 0 (words (bank 0 1 1)) initial :=
  (Table.Institution.rtl_divOracle_iff accepted (bank 0 1 1) initial).mpr spinAbsent

example {targets : Checked.Phi.Targets} (accepted : Table.lowerChecked dependent = some targets)
    (initial : Memory) :
    Observation.diverge initial ∈ ssaBeh 1
      (inputModel (P := Rows.wordSignature) model Memory (bank 0 1 1))
      (Table.Institution.scope accepted) ↔
    Behavior.diverges ∈ Table.Institution.rtlBehaviors (bank 0 1 1) initial targets.1 :=
  Table.Institution.rtl_room_observation_iff accepted (bank 0 1 1) (.diverge initial)

example {targets : Checked.Phi.Targets} (accepted : Table.lowerChecked dependent = some targets)
    (perm : Rows.InputPermutation 3) :
    ∃ after, Table.lowerChecked (Table.reindexCaptures perm dependent) = some after :=
  Table.lowerChecked_reindex perm accepted

#eval do
  let swap : Rows.InputPermutation 3 := Equiv.swap 0 2
  let (rtl, ssa) ← Table.lowerChecked (Table.reindexCaptures swap dependent)
  let input := bank 5 2 6
  let mem := Memory.ofList 4 [29, 71, 53, 11]
  let machine := (rtl.runMain 10 0 (words input) mem).returnedValues?
  let typed := (Generic.Fuel.run model (inputEnv model input) 2 ssa).bind fun (_, packet) =>
    (Generic.Fuel.decodeArgs model [word] packet).map fun fields => Silmaril.SSA.RVSDG.Tuple.get fields .head
  pure (machine.map (List.map BitVec.toInt), typed.map BitVec.toInt)
-- some (some [7], some 7)

#eval do
  let identify : Rows.InputMap 3 := fun slot => if slot = 2 then 0 else slot
  let (rtl, ssa) ← Table.lowerChecked (Table.mapCaptures identify dependent)
  let input := bank 5 2 6
  let mem := Memory.ofList 4 [29, 71, 53, 11]
  let machine := (rtl.runMain 13 0 (words input) mem).returnedValues?
  let typed := (Generic.Fuel.run model (inputEnv model input) 3 ssa).bind fun (_, packet) =>
    (Generic.Fuel.decodeArgs model [word] packet).map fun fields => Silmaril.SSA.RVSDG.Tuple.get fields .head
  pure (machine.map (List.map BitVec.toInt), typed.map BitVec.toInt)
-- some (some [6], some 6)
```

The two results are `6 - 5 = 1` and `1 + 2 = 3`, so the bank enters as
`(1, 3, 5)` and feeds back `(4, 3, 5)` before returning 7. Using captured
2 as the entry stride returns 5 instead. A captured stride in the feedback
column and a literal in the producer table both fail the check.

## Unbounded partial observations

`Table.denotations_eq` in `Table.Denotation.Thms` identifies each checked target's
`Part (Word × Memory)` with the native partial word paired with the whole
initial memory. The RTL observer selects a singleton return from the
program's call oracle. The λSSA observer selects an exit-zero packet and
final memory from actual Region evaluation. Determinism makes each
witness unique.

Use `mem_rtlDenote_iff_runMain` with an RTL instruction budget and
`mem_lambdaDenote_iff_run` with a λSSA visit budget. The partial
observations range over all finite witnesses. `denotations_none_iff`
relates `Part.none` in each target to no finite native return.
In the regression, input `(0, 1, 1)` initializes `(-1, 0, 1)`.
That bank takes a backedge to itself on every activation, so both target
observations are undefined. The observers describe finite word returns
in this profile. [Return and fixed-point checks][table-regression]

## Satisfaction of observation equations

`Table.Institution.program` and `equation` package checked graphs at the
existing native word signature. The two sides share their typed input
and result sorts. Their producer signatures can differ internally.
`equation_holds_iff` compares the native equation with the existing
`Observational.Sentence.eq` on the emitted RTL and scoped λSSA.
At each typed input and common initial memory, the observations contain
each returned word and its entire final memory. The same theorem gives
a cross-backend comparison, and `equation_at_iff` states the pointwise law.

`room_ret_iff` describes every return in the existing λSSA room. Its exit
is zero, the payload packs the native word, and the final memory equals
the initial memory. `room_other_exit_absent` and `room_fault_absent` give
the corresponding exclusions. The concrete word room model has no
primitive faults.

`room_diverges_iff` identifies the room's divergence observation with
undefined native denotation. From a bank with no finite return, the total
header must choose a backedge and the next bank still has no finite return.
The proof coinducts on these actual λSSA transitions using the entry and
header packet laws. Deterministic finite evaluation excludes divergence in
the other direction.

`room_equation_at_iff` and `room_equation_holds_iff` compare native equations
with the full room at the concrete word signature, pointwise and across all
typed inputs respectively. Room satisfaction compares all initial and final
memories. The initial memory passed to the theorem supplies one witness for
reflection through the return projection. On `(6, 2, 5)` the room observes
return 7 with unchanged memory. On `(0, 1, 1)` it observes divergence.
Changing the first preheader subtraction to addition makes the alternative
graph return 3 at that same input, so the room equation fails.
[Checked regression][table-regression]

### Full RTL.SSA behaviours

`rtlBehaviors` collects the existing `RTL.SSA.Behaves` outcomes from
function zero's actual start. `rtl_start_exists` certifies the start
for every typed input and initial memory. `rtl_behavior_iff` classifies
all outcomes. Returns contain exactly one native word with the entire
initial memory. `rtl_no_fault` excludes both traps and stuck states.

`rtl_divOracle_iff` relates native undefinedness to an infinite sequence
of machine instructions. The proof follows the emitted entry and then
the nonempty instruction path for each taken backedge. A header with
no finite native return must take that backedge, and the successor
bank still has no finite return. Determinism excludes divergence when
the machine has a finite return. Bounded `runMain` still reports a
running state when its instruction budget is exhausted.

`rtl_equation_at_iff` and `rtl_equation_holds_iff` compare native
equations with full RTL behaviour equations at one typed input or all
typed inputs, with a common initial memory. The regression checks
return 7, divergence on the fixed-point input, and a failed RTL equation
when the other side returns 3 at that input. [Checked regression][table-regression]

### Comparing the emitted backends

`rtl_room_observation_iff` compares the full room with actual RTL outcomes
at the memory recorded in each room observation. An exit-zero packet
and a singleton RTL return carry the same word and the entire initial
memory. Divergence observations correspond in both directions.
`rtl_room_return_iff` queries an exact word and final memory directly.

`rtl_room_equation_at_iff` compares actual RTL equation satisfaction at a
shared typed input and initial memory with full room satisfaction at
that input. For the checked pure profile, one common initial memory
suffices to reflect the room equation, which ranges over all memories.
`rtl_room_equation_holds_iff` quantifies the comparison over typed inputs.
The regression pairs return 7 and fixed-point divergence across both
backends and checks the mismatch when RTL returns 3 and the other
emitted region diverges. [Checked regression][table-regression]

These comparisons are at the concrete dependent-preheader word signature.
`terminates_holds_iff` relates the native termination sentence to a
nonempty return set at every typed input.

### Permuting dependent-preheader captures

`Table.reindexCaptures` uses the typed `Rows.InputPermutation` on external
reads in the preheader producer table and the entry column. Earlier producer
references, header bank slots and incoming occurrences retain their identity.
`Table.initial_reindex` proves the whole entry latch commutes with
`perm.pull`. `Table.denote_reindex` extends this to the native partial
result of a recognized graph.

Run the ordinary `Table.lowerChecked` on the mapped graph to re-emit both
targets. `Table.lowerChecked_reindex` proves acceptance from the original
successful check. The existing computed-initializer requirement and supported
opcode checks still apply. The typed entry reads remain in scope at each
instruction, and the header and exit keep their original checks.
`Table.lowerChecked_reindex_iff` reflects acceptance by applying the inverse
permutation.

`Table.reemit_observations` takes just the original success and supplies the
new checker result together with full RTL and λSSA observation equality
at every pulled valuation. This includes exact returns with unchanged
memory and actual divergence.

`Table.reindex_equation_at_iff` compares each re-emitted equation at the
pulled valuation. The all-input law covers every old valuation because
`InputPermutation.pull_symm` supplies an inverse. In the regression,
swapping captures 0 and 2 reverses the subtraction operands and redirects
the entry limit. Input `(5, 2, 6)` now returns 7, and `(1, 1, 0)` reaches
the fixed point on both targets. The original machine returns 3 at
`(1, 1, 0)`. A typed table whose entry uses only raw captures is refused
before and after permutation. [Checked regression][table-regression]

### Identifying dependent-preheader captures

`Rows.InputMap` maps old word slots to new slots in the same typed interface.
`Table.mapCaptures` applies it to the dependent producer reads and entry
column. The carried bank retains its width and occurrence routing. In the
example, old slots 0 and 2 both read new slot 0, leaving new slot 2 unused.

`Table.lowerChecked_mapCaptures` proves forward acceptance through the
ordinary checker. `Table.reemit_mapped_observations` uses that check to
compare actual RTL and λSSA observations at the pulled valuation, including
returns with the whole initial memory and genuine divergence. The inverse
acceptance and global equation laws above apply to permutations.

`Table.mapCaptures_equation_holds_iff` tests the original equation only on
the image of `InputMap.pull`. The fixture compares two dependent preheaders
whose first subtractions read `0 - 2` and `2 - 2`, where the numbers name
capture slots. At `(6, 2, 5)` they originally return 7 and 6. After capture
identification they agree at every new valuation because pulled slots 0
and 2 are equal. At new input `(5, 2, 6)` both emitted targets return 6
with the whole initial memory. At `(1, 0, 42)` both diverge at the fixed
point. [Checked regression][table-regression]

```sh
lake build --wfail +Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Fuel.Thms \
  +Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Regression \
  +Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Regression \
  +Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Regression \
  +Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Fuel.SignedGuardRegression \
  +Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Fuel.BankOperandRegression \
  +Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Fuel.ComputedExitRegression \
  +Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Fuel.Regression \
  +Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Regression \
  +Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Regression
```

[pair]: https://github.com/hiloopai/silmaril-lean/pull/3707
[row]: https://github.com/hiloopai/silmaril-lean/pull/3608
[phi]: https://github.com/hiloopai/silmaril-lean/pull/3631
[regression]: ../../Silmaril/Proofs/Machine/SeaOfNodes/Loop/RTL/Routing/Guarded/Rows/Regression.lean
[thms]: ../../Silmaril/Machine/SeaOfNodes/Loop/RTL/Routing/Guarded/Rows/Thms.lean
[fuel-thms]: ../../Silmaril/Machine/SeaOfNodes/Loop/RTL/Routing/Guarded/Rows/Fuel/Thms.lean
[fuel-regression]: ../../Silmaril/Proofs/Machine/SeaOfNodes/Loop/RTL/Routing/Guarded/Rows/Fuel/Regression.lean
[computed-regression]: ../../Silmaril/Proofs/Machine/SeaOfNodes/Loop/RTL/Routing/Guarded/Rows/Fuel/ComputedExitRegression.lean
[operand-regression]: ../../Silmaril/Proofs/Machine/SeaOfNodes/Loop/RTL/Routing/Guarded/Rows/Fuel/BankOperandRegression.lean
[native-result]: ../../Silmaril/Proofs/SSA/SeaOfNodes/Loop/Regression.lean
[institution-thms]: ../../Silmaril/Machine/SeaOfNodes/Loop/RTL/Routing/Guarded/Rows/Institution/Thms.lean
[simple-two-expressions]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter13/src/test/java/com/seaofnodes/simple/Chapter13Test.java#L169-L173
[simple-lt]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter13/src/main/java/com/seaofnodes/simple/node/BoolNode.java#L72
[signed-regression]: ../../Silmaril/Proofs/Machine/SeaOfNodes/Loop/RTL/Routing/Guarded/Rows/Fuel/SignedGuardRegression.lean
[native-guard-regression]: ../../Silmaril/Proofs/Machine/SeaOfNodes/Loop/RTL/Routing/Guarded/Rows/Native/Regression.lean
[simple-latch]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/GraphEvaluator.java#L93-L110
[preheader-regression]: ../../Silmaril/Proofs/Machine/SeaOfNodes/Loop/RTL/Routing/Guarded/Rows/Native/Preheader/Regression.lean
[table-regression]: ../../Silmaril/Proofs/Machine/SeaOfNodes/Loop/RTL/Routing/Guarded/Rows/Native/Preheader/Table/Regression.lean
