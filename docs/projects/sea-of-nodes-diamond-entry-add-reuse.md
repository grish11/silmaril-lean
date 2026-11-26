# Reuse a checked entry add in a materialized diamond

`Materialize.EntryReuse.rewrite?` takes the actual right-materialized
program and one typed producer nomination in its common entry table.
It checks the emitted suffix for literal `k`, inner `capture + phi`,
and return of `inner + k`. The nomination must have the existing typed add
key with the original capture argument on the left. On the right
it must have a shared word that the original Φ forwards in both
actual predecessor occurrences. The check compares addresses after
lifting the shared wire into each arm's full scope. A branch-local
producer cannot serve as the entry nomination. `rewriteAt?` resolves
a numbered nomination only in the shared table.
[Checker and emitter](../../Silmaril/SSA/SeaOfNodes/Diamond/AddPhi/Rotate/Pair/Dispatch/Materialize/EntryReuse/Defs.lean)

The emitted graph forwards the entry result in a new first join
column and keeps the original Φ operands in the second column. The
shared table, original capture, predicate, arms and Region order
are carried through. The suffix retains its literal and the existing
outer add, whose left operand is now the forwarded entry result.
The old inner result routes to that boundary value and the outer
result shifts down one binding.

`check_provenance` proves exact ordered key and occurrence-wire
identity. `emit_agrees` and `emit_packet_eq` preserve every routed
read and all values of a supplied outgoing packet, including
additional reads of the original Φ or the elided inner result.
`rewrite?_returns_iff` compares the emitted program with the
materialized intermediate. `materialize_then_reuse_returns_iff`
compares it with the original two-Φ program for every typed input.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Diamond/AddPhi/Rotate/Pair/Dispatch/Materialize/EntryReuse/Thms.lean)

Cliff Click's *Global Code Motion/Global Value Numbering*, PLDI ’95,
§3.1 step 3, provides the exact-key replacement and removal precedent.
Here availability comes from the common entry table of the native
diamond, and the existing `Producer.read_key` law supplies the
ordered add semantics. This slice checks one nominated shared add
and one emitted suffix shape. General dominance queries, code motion,
extra equivalences and iterative GVN are outside the profile.
[PLDI ’95](https://doi.org/10.1145/207110.207154) ·
[Paper pin and acyclic GVN proof](sea-of-nodes/optimization/sea-of-nodes-gvn-pass.md)

```lean
module

import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Thms
import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Discovery.Thms
import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Commutative.Thms
import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.ValueNumbers.Thms
meta import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Defs
meta import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Discovery.Defs
meta import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Commutative.Defs
meta import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.ValueNumbers.Defs

open Silmaril.SSA.SeaOfNodes.Diamond
open AddPhi.Rotate.Pair.Dispatch (Column Refusal)
open AddPhi.Rotate.Pair.Dispatch.Materialize
open AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse (rewriteAt?)
open AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Discovery (discoverAndRewrite?)
open Silmaril.SSA.SeaOfNodes.Pure.SubZero (model word wordPort)
open Silmaril.SSA.RVSDG (Tuple)

def sample : AddPhi.Pair.Source [.predicate, word, word] [[wordPort], [wordPort]] where
  shared := .cons (.literal 7) .nil
    (.cons .add (.cons (.arg (.tail (.tail .head))) (.cons (.arg (.tail .head)) .nil)) .nil)
  predicate := .arg .head
  merge := ⟨.onFalse⟩
  arms := fun _ => {
    sigs := [], dataflow := .nil
    outputs := .cons (.arg (.tail .head)) (.cons (.output (0 : Fin 2) .head) .nil) }

def run (guard : Bool) : Except Refusal (Option (Nat × BitVec 64)) :=
  (rewrite sample (.tail (.tail .head)) .left).map fun result => do
    let .materialized .right _ emitted := result | none
    let target ← rewriteAt? emitted (.output 1 0)
    let entry : Tuple (Val model.value) (dataPorts [.predicate, word, word]) :=
      .cons ⟨guard⟩ (.cons (3 : BitVec 64) (.cons (0xffffffffffffffff : BitVec 64) .nil))
    pure (target.suffix.sigs.length, target.denote entry)

#eval (run false, run true)

example : (run false, run true) = (.ok (some (2, 9)), .ok (some (2, 9))) := rfl

def discover : Except Refusal (Option (List Silmaril.SSA.RVSDG.Address × Nat)) :=
  (rewrite sample (.tail (.tail .head)) .left).map fun result => do
    let .materialized .right _ emitted := result | none
    let target ← discoverAndRewrite? emitted
    pure ((target.diamond.arms .first).outputs.addresses, target.suffix.sigs.length)

#eval discover

example : discover = .ok (some ([.output 1 0, .arg 1], 2)) := rfl

def reversed : AddPhi.Pair.Source [.predicate, word, word] [[wordPort], [wordPort]] :=
  { sample with
    shared := .cons (.literal 7) .nil
      (.cons .add (.cons (.arg (.tail .head)) (.cons (.arg (.tail (.tail .head))) .nil)) .nil) }

def compareModes : Except Refusal (Option (Bool × Bool)) :=
  (rewrite reversed (.tail (.tail .head)) .left).map fun result => do
    let .materialized .right _ emitted := result | none
    pure ((discoverAndRewrite? emitted).isSome,
      (EntryReuse.Commutative.discoverAndRewrite? emitted).isSome)

#eval compareModes

example : compareModes = .ok (some (false, true)) := rfl

def discoverByValue {inputs : List (ValueSort Unit)} {sigs : List (List (Ty Unit))}
    (g : AddPhi.Pair.Source inputs sigs) (capture : AddPhi.Rotate.InputWord inputs)
    (first : Column) : Except Refusal (Option (AddPhi.Rotate.Program inputs sigs [word, word])) :=
  (rewrite g capture first).map fun result => do
    let .materialized .right _ emitted := result | none
    EntryReuse.ValueNumbers.discoverAndRewrite? emitted

example : (discoverByValue sample (.tail (.tail .head)) .left).map (·.isSome) = .ok true := rfl
```

The regression additionally uses unequal arm scopes and checks a
three-field outgoing packet. It refuses a same-shaped add available
only on the second arm and a Φ that reads a different input on that
occurrence.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Diamond/AddPhi/Rotate/Pair/Dispatch/Materialize/EntryReuse/Regression.lean)

## Discover a representative

`EntryReuse.Discovery.discoverAndRewrite?` takes the emitted program
and needs no producer nomination. It scans typed word producers in the
common entry table using the existing GVN enumeration. The first
producer in definition order whose exact operands pass both occurrence
checks wins. The call delegates to `EntryReuse.rewrite?` for the suffix
shape check and emission. Failure means that every typed shared producer
would be refused by that nomination API, which also covers suffixes
outside the right-materialized profile.

`findRepresentative?_eq_some_iff` characterizes the tie-break and
`discoverAndRewrite?_eq_none_iff` states the scope of search failure.
`discoverAndRewrite?_packet_eq` and
`materialize_then_discover_returns_iff` reuse the checked emitter's
packet and finite-return laws. The discovery regression skips an earlier
add with reversed operands and checks that the earlier of two accepted
adds supplies the new join column on both actual occurrences. The same
fixture exercises wrapping arithmetic and refuses an arm-local-only
match and a mismatched second occurrence. This scan covers one
right-materialized join suffix and its shared entry table.
[Discovery theorems](../../Silmaril/SSA/SeaOfNodes/Diamond/AddPhi/Rotate/Pair/Dispatch/Materialize/EntryReuse/Discovery/Thms.lean) ·
[Discovery regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Diamond/AddPhi/Rotate/Pair/Dispatch/Materialize/EntryReuse/Discovery/Regression.lean)

## Opt in to commutative add matching

Click’s PLDI ’95 §3.1 step 3 specifies hashing and comparing commutative
instructions independently of operand order.
`EntryReuse.Commutative.discoverAndRewrite?` implements the comparison
for wrapping i64 addition in this right-materialized profile. It chooses
the first shared entry add in definition order whose operands match in
either orientation **at each actual incoming occurrence**. Each test
compares the capture and the actual Φ operand by exact typed source
identity. `GVN.Key.matches` and the ordered discovery API retain their
ordered comparison. [PLDI ’95 paper pin](sea-of-nodes/optimization/sea-of-nodes-gvn-pass.md)

`check_provenance` gives the exact typed pairing per occurrence.
`check_agrees` proves that the representative reads the same wrapping sum
using the existing typed producer evaluation law and `BitVec.add_comm`.
Both modes use the same emitter and route. The commutative theorems
preserve complete packets on each occurrence and finite returns from
the original diamond for every typed input. The regression accepts a
reversed shared add in commutative mode and rejects a source mismatch
on the second occurrence even when both inputs happen to read the same
value. The extension covers word addition and the existing right-materialized
suffix and has no dependency on a general key normalization or hash table.
[Commutative theorems](../../Silmaril/SSA/SeaOfNodes/Diamond/AddPhi/Rotate/Pair/Dispatch/Materialize/EntryReuse/Commutative/Thms.lean) ·
[Commutative regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Diamond/AddPhi/Rotate/Pair/Dispatch/Materialize/EntryReuse/Commutative/Regression.lean)

## Compare producer value numbers

Click's PLDI ’95 §3.1 step 3 compares operations using their already
numbered inputs. `EntryReuse.ValueNumbers.discoverAndRewrite?` checks
an ordered entry add by comparing structural value numbers in the
right-materialized diamond. The numbers are uninterned trees containing
typed argument positions, exact word literals, and binary opcodes with
ordered child numbers. The native evaluator builds them in producer
order using the wrapping i64 literal, add, subtract and multiply
signature. [PLDI ’95 paper pin](sea-of-nodes/optimization/sea-of-nodes-gvn-pass.md) ·
[Word number evaluator and read law](../../Silmaril/SSA/SeaOfNodes/GVN/WordNumber/Thms.lean)

The representative's operands come from its existing typed GVN key and
are numbered in the dominating shared table. Each actual Φ input is
numbered in its own arm, seeded with that shared store. The first
accepted shared add in definition order supplies the forwarded result.
`check_pairing` proves structural equality at each occurrence,
`phiKey_eval` links its number to the selected Phi value, and
`check_agrees` gives equality of the inner sum for all typed inputs.
Both complete packet and finite-return theorems use the existing
emitter. The supported profile is finite, acyclic, and uses one
right-materialized suffix.
[Value-number reuse theorems](../../Silmaril/SSA/SeaOfNodes/Diamond/AddPhi/Rotate/Pair/Dispatch/Materialize/EntryReuse/ValueNumbers/Thms.lean)

The regression reuses a shared add when two separate arm chains each
compute `(y + z) * y` on a reversed Region, and verifies the forwarded
addresses and wrapping results. Changing one nested input on the second
occurrence blocks reuse, even when one input valuation makes the
distinct expressions agree.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Diamond/AddPhi/Rotate/Pair/Dispatch/Materialize/EntryReuse/ValueNumbers/Regression.lean)

```sh
topic=SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse
make check CHECK_TARGETS="+Silmaril.$topic.ValueNumbers.Thms +Silmaril.Proofs.$topic.ValueNumbers.Regression +Silmaril.Proofs.$topic.Commutative.Regression +Silmaril.Proofs.$topic.Discovery.Regression +Silmaril.Proofs.$topic.Regression"
```
