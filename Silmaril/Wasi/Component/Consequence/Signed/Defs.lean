module

public import Silmaril.Wasi.Component.Consequence.Gentzen.Defs
public import Silmaril.Wasm.Game.Accept.Export.Defs

/-! # Signed and two-sided observation protocols

Three more protocols over component event traces (`Silmaril.Wasi.Consequence.Reading`), whose
readings are Gentzen sequent relations or lists of signed formulas
(`Silmaril.Consequence.Signed`, `Silmaril.Consequence.Gentzen.Seq`). Every reading is total over
traces: a strategy `σ` gives `Traces σ`, and a reading gives a relation. Nothing here is a
compiled component.

## (1) Imported `pos(v)`, `neg(v)`, `done()`, optional `reset()`: batches

The component emits signed literals by calling its imports `pos` and `neg`, and closes a batch by
calling `done`. `importBatch b fns decV td` reads each `done` as the claim of the batch of literals
emitted since startup, the previous `done`, or the last `reset`, in order and with multiplicity:

* the batch is the state **before** the `done` (`stateful` reads the prefix), and `done` then starts
  the next batch (it is a `Step.reset`);
* a trailing batch with no `done` is never emitted, and `reset` discards the open batch;
* at `Boundary.call` the reading records the component's **requests**. At `Boundary.answer` it
  records the **non-trapping host answers**: a literal whose host call traps is not recorded, and
  a `done` whose host call traps is answered `trap` (no batch is emitted). Whether that failed
  `done` still closes the batch is the explicit `TrapDone` policy. The two boundaries are
  different projections of the same plays: they agree only under hypotheses on the hosts (no trap),
  which are not assumed.

`batches T r` is the predicate of emitted lists. `batchFinset T r s` is the **existential**
finite-set reading: some emitted list has the members `s`. It is not equal to `batches` up to a
permutation-and-duplication quotient unless `batches` is invariant under it, which is not assumed.
`batchUnsat` and `batchTaut` are the raw Gentzen UNSAT and TAUTO readings of `batches`
(`Silmaril.Consequence.Gentzen.viaUnsat`, `viaTauto`, through `swap` and the list-checker
readings `unsatSeq`, `tautSeq`).

## (2) Exported `check(conj: list v, disj: list v) -> bool`

`seqCheck f decΓ decΔ` reads a `true` return of `check` on the arguments `(Γ, Δ)` as the sequent
`Γ ⊢ Δ` (`seqOf`). The signed variant is the same reading at `V := Signed W`; the single-list
signed checker is the merged `listCheck` with `unsatSeq` and `tautSeq`.

**Core modules** have no WIT arguments: `coreSeq P Hosts m name enc` reads the module's export
`name(ptr: i32, len: i32) -> i32` (`Silmaril.Wasm.Game.Accept.exportAccepted`) through an explicit,
partial byte codec `enc : List UInt8 → List UInt8 → Option (List UInt8)`. The typed configuration
(`name`, `enc`) is separate from the runtime quantifiers (the profile `P` and the host set
`Hosts`). `memberEnc` is the codec of `Silmaril.Wasm.Examples.MemberCheck`: `Γ ⊢ [c]` is the input
`c :: Γ`, and other succedents are not encoded (`none`, so not accepted).

## (3) Exported `assume(v)`, `assert(v)`, `check() -> bool`, optional `reset()`

`exportAssumeAssert b fns decV snap` accumulates **both** sides: `assume` appends to the context
and `assert` to the succedent (`Policy.pairList`), `reset` starts a new epoch, and a `check`
return reads the sequent of its snapshot. `SnapshotAt.ret` reads the state of the whole prefix
before the return; `SnapshotAt.call` reads the state before the last call of `check`. Legal plays
alternate export calls and returns (`Silmaril.Wasi.World.Exports`), so no `assume` can occur
between them, but no theorem here identifies the two snapshots. Here `assert` names an
**observation** (an event that adds a formula to the succedent), not a proof of anything.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasi.Consequence

open Silmaril.Consequence (Signed)
open Silmaril.Wasm.Component (Val)

universe u v

variable {X : Type u} {C : Type v} {F V : Type}

/-! ## Generic -/

/-- Exchange the two sides of a reading. -/
def swap (r : Reading X C) : Reading C X := fun s e =>
  (r s e).map fun q => (q.2.1, q.1, q.2.2)

/-- The predicate of a reading with no statement: some play accepts `x`. -/
def predOf (T : Set (List WEv)) (r : Reading X Unit) : X → Prop := fun x => Accepted T r x ()

/-- The sequent relation of a two-list reading: `Γ ⊢ Δ` iff some play accepts `(Γ, Δ)`. -/
def seqOf (T : Set (List WEv)) (r : Reading (List F) (List F)) :
    Silmaril.Consequence.Gentzen.Seq F :=
  fun Γ Δ => Accepted T r Γ Δ

/-- The sequent relation of a reading of pairs: `Γ ⊢ Δ` iff some play accepts `((Γ, Δ), ())`. -/
def pairSeqOf (T : Set (List WEv)) (r : Reading (List F × List F) Unit) :
    Silmaril.Consequence.Gentzen.Seq F :=
  fun Γ Δ => Accepted T r (Γ, Δ) ()

/-! ## (1) Batches of signed literals -/

/-- The imports of the batch protocol. -/
structure BatchFns where
  /-- `pos(v)`: emit `+v`. -/
  pos : FnName
  /-- `neg(v)`: emit `-v`. -/
  neg : FnName
  /-- `done()`: close the batch. -/
  done : FnName
  /-- `reset()`, when the protocol has one: discard the open batch. -/
  reset : Option FnName := none

/-- Whether a `done` whose host call traps closes the batch (at `Boundary.answer`). -/
inductive TrapDone where
  /-- A trapped `done` leaves the batch open. -/
  | keep
  /-- A trapped `done` discards the batch. -/
  | consume
  deriving DecidableEq, Repr

/-- The signed literal of an emitting call. -/
def BatchFns.literal (fns : BatchFns) (decV : List Val → Option V) (g : FnName)
    (args : List Val) : Option (Signed V) :=
  if g = fns.pos then (decV args).map .pos
  else if g = fns.neg then (decV args).map .neg
  else none

/-- `g` is `done` or the reset, with no arguments. -/
def BatchFns.closes (fns : BatchFns) (g : FnName) (args : List Val) : Prop :=
  args = [] ∧ (g = fns.done ∨ fns.reset = some g)

instance (fns : BatchFns) (g : FnName) (args : List Val) : Decidable (fns.closes g args) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- **The observed steps of the batch protocol**: literals add, `done` and `reset` restart. -/
def batchStep (b : Boundary) (fns : BatchFns) (decV : List Val → Option V) (td : TrapDone) :
    WEv → Option (Step (Signed V))
  | .req g args =>
    if b = .call then
      if fns.closes g args then some .reset else (fns.literal decV g args).map .add
    else none
  | .imp g args res =>
    if b = .answer then
      if fns.closes g args then
        if res.isSome ∨ (td = .consume ∧ g = fns.done) then some .reset else none
      else if res.isSome then (fns.literal decV g args).map .add else none
    else none
  | _ => none

/-- **The claims of the batch protocol**: a `done`, at the boundary. -/
def batchClaim (b : Boundary) (fns : BatchFns) : WEv → Option (Unit × Answer)
  | .req g [] => if b = .call ∧ g = fns.done then some ((), .yes) else none
  | .imp g [] res =>
    if b = .answer ∧ g = fns.done then some ((), if res.isSome then .yes else .trap) else none
  | _ => none

/-- **Protocol: imported `pos`/`neg`/`done`.** A `done` claims the batch before it. -/
def importBatch (b : Boundary) (fns : BatchFns) (decV : List Val → Option V) (td : TrapDone) :
    Reading (List (Signed V)) Unit :=
  stateful Policy.list (batchStep b fns decV td) (batchClaim b fns)

/-- The emitted batches: lists, in order and with multiplicity. -/
abbrev batches (T : Set (List WEv)) (r : Reading (List (Signed V)) Unit) :
    List (Signed V) → Prop :=
  predOf T r

/-- The existential finite-set reading: some emitted batch has the members `s`. -/
def batchFinset [DecidableEq V] (T : Set (List WEv)) (r : Reading (List (Signed V)) Unit)
    (s : Finset (Signed V)) : Prop :=
  ∃ l, l.toFinset = s ∧ batches T r l

/-- **The UNSAT reading of the batches**: `Γ ⊢ Δ` iff `Γ ++ Δ.map neg` was emitted. -/
def batchUnsat (T : Set (List WEv)) (r : Reading (List F) Unit) (neg : F → F) :
    Silmaril.Consequence.Gentzen.Seq F :=
  unsatSeq T (swap r) neg

/-- **The TAUTO reading of the batches**: `Γ ⊢ Δ` iff `Γ.map neg ++ Δ` was emitted. -/
def batchTaut (T : Set (List WEv)) (r : Reading (List F) Unit) (neg : F → F) :
    Silmaril.Consequence.Gentzen.Seq F :=
  tautSeq T (swap r) neg

/-! ## (2) Two-list checks -/

/-- **Protocol: exported `check(conj: list v, disj: list v) -> bool`.** -/
def seqCheck (f : FnName) (decΓ decΔ : Val → Option (List V)) : Reading (List V) (List V) :=
  exportCheck f (args2 decΓ decΔ)

/-- **A core module's export as a sequent relation**, through an explicit partial byte codec. -/
def coreSeq (P : Silmaril.Wasm.Numerics.Profile)
    (Hosts : Set (Silmaril.Wasm.Execution.Core.HostSemantics Nat)) (m : Silmaril.Wasm.Module)
    (name : String) (enc : List UInt8 → List UInt8 → Option (List UInt8)) :
    Silmaril.Consequence.Gentzen.Seq UInt8 :=
  fun Γ Δ => ∃ w, enc Γ Δ = some w ∧ w ∈ Silmaril.Wasm.Game.Accept.exportAccepted P Hosts m name

/-- The codec of `Silmaril.Wasm.Examples.MemberCheck`: `Γ ⊢ [c]` is `c :: Γ`; nothing else. -/
def memberEnc : List UInt8 → List UInt8 → Option (List UInt8)
  | Γ, [c] => some (c :: Γ)
  | _, _ => none

/-! ## (3) Assume, assert, check -/

/-- The exports of the assume/assert protocol. -/
structure AssumeAssertFns where
  /-- `assume(v)`: add `v` to the context. -/
  assume : FnName
  /-- `assert(v)`: add `v` to the succedent (an observation, not a proof). -/
  assert : FnName
  /-- `check() -> bool`. -/
  check : FnName
  /-- `reset()`, when the protocol has one. -/
  reset : Option FnName := none

/-- Which state a `check` return reads. -/
inductive SnapshotAt where
  /-- The state of the whole prefix before the return. -/
  | ret
  /-- The state before the last call of `check`. -/
  | call
  deriving DecidableEq, Repr

/-- Append to the context (`inl`) or to the succedent (`inr`). -/
def Policy.pairList {W : Type} : Policy (W ⊕ W) (List W × List W) :=
  ⟨([], []), fun s x => match x with
    | .inl a => (s.1 ++ [a], s.2)
    | .inr d => (s.1, s.2 ++ [d])⟩

/-- The observed steps of the assume/assert protocol, at `b`. -/
def pairStep (b : Boundary) (fns : AssumeAssertFns) (decV : List Val → Option V) :
    WEv → Option (Step (V ⊕ V))
  | .call g args => if b = .call then pairStepAt fns decV g args else none
  | .ret g args (some _) => if b = .answer then pairStepAt fns decV g args else none
  | _ => none
where
  /-- The step of a call of `g` on `args`. -/
  pairStepAt (fns : AssumeAssertFns) (decV : List Val → Option V) (g : FnName)
      (args : List Val) : Option (Step (V ⊕ V)) :=
    if args = [] ∧ fns.reset = some g then some .reset
    else if g = fns.assume then (decV args).map (.add ∘ .inl)
    else if g = fns.assert then (decV args).map (.add ∘ .inr)
    else none

/-- The prefix before the last call of `f` with no arguments (all of `s` if there is none). -/
def beforeLastCall (f : FnName) (s : List WEv) : List WEv :=
  match (s.reverse.dropWhile fun e => !isCallOf e) with
  | [] => s
  | _ :: t => t.reverse
where
  /-- A call of `f` with no arguments. -/
  isCallOf : WEv → Bool
    | .call g [] => g == f
    | _ => false

/-- **Protocol: exported `assume`/`assert`/`check`.** A `check` return claims the sequent of
its snapshot. -/
def exportAssumeAssert (b : Boundary) (fns : AssumeAssertFns) (decV : List Val → Option V)
    (snap : SnapshotAt) : Reading (List V × List V) Unit := fun s e =>
  match e with
  | .ret g [] res =>
    if g = fns.check then
      some (epochState Policy.pairList
        ((if snap = .ret then s else beforeLastCall fns.check s).filterMap (pairStep b fns decV)),
        (), .ofResult res)
    else none
  | _ => none

end Silmaril.Wasi.Consequence
