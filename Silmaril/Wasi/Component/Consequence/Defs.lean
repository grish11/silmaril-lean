module

public import Silmaril.Wasi.Component.Accept.Defs
public import Silmaril.Logic.Szs.Defs
public import Mathlib.Data.Finset.Insert

/-! # Components as consequence checkers: four protocols and their readings

A component (`Silmaril.Wasi.Accept`: a strategy over named events `WEv`, its plays ranging over
every host and every caller) is read as a **consequence relation** `X → C → Prop` between
assumptions `x : X` and statements `c : C`. Four protocols, each with an explicit observation
boundary:

1. **Exported `check(ax, stmt) -> bool`** (`exportCheck`): a return of `check` is the query
   `(ax, stmt)` with its answer.
2. **Exported `axiom(v)` / `check(stmt) -> bool`, optional `reset()`** (`exportStateful`): the
   assumptions are the `axiom` calls since the last `reset`, accumulated by an update policy.
3. **Imported `assert(ax, stmt)`** (`importAssert`): the component claims `(ax, stmt)` by
   calling the host.
4. **Imported `assume(v)` / `assert(stmt)`, optional `reset()`** (`importStateful`).

## Observation boundaries

* An export query is observed **at its return** (`WEv.ret`). Its `Answer` is `yes` (returns
  `true`), `no` (returns `false`: a *successful false*), `trap` (the call traps) or `other`
  (returns anything that is not one `bool`). A call that never returns has no return event: in
  these finite-play models **divergence is the absence of an answer**, never an answer
  (`Silmaril.Games` has infinite plays; they are not used here).
* An assumption, a reset or an import claim is observed by `Boundary`: `.call` at its request
  (`WEv.call` for exports, `WEv.req` for imports), `.answer` at its non-trapping answer
  (`WEv.ret … (some _)`, `WEv.imp … (some _)`). An import claim observed at `.answer` whose host
  traps is answered `trap`; at `.call`, an import claim is always `yes` (there is no negative
  observation of a call).

## Readings, relations and statuses

A `Reading X C` reads the last event of a play prefix as a query. From a set of event traces `T`
(for a component, `Silmaril.Wasi.Accept.Traces σ`):

* `Accepted T r x c`: **some** completed query `(x, c)` answers `yes` — existential over plays,
  hence over hosts and callers. `AcceptWitness T r x c : Type` is the play itself; its
  `Nonempty` is `Accepted` (`Silmaril.Wasi.Consequence.nonempty_acceptWitness_iff`).
* `execProblem T r x c`: the **execution model** as an SZS problem (`Silmaril.Logic.Szs`): the
  interpretations are completed queries `(prefix, event)`, the models of `Ax` are the completed
  queries `(x, c)` of `T`, the models of `C` those answering `yes`. Existential acceptance is its
  `Current.SAT`, not its `THM`; its `THM` is the universal reading (every completed query, under
  every host and caller, answers `yes`), and holds vacuously when no query completes (`CAX`).
  `classify` picks the one of `CAX`, `STH`, `SCT`, `NOC` that holds; `status` pairs it with the
  Prop consequence.
* `Sound R target` / `Complete R target`: inclusion in a target system, kept separate from
  acceptance and status.

## State and reset epochs

The stateful protocols fold the observed `Step`s (`add a`, `reset`) of the prefix by a named
update `Policy`: `list` (append, in order, with duplicates), `finset` (insert), `count` (the
number of assumptions, `Nat`), `named` (keyed assumptions `K × V` into `K → Option V`, last write
wins) and `namedFirst` (first write wins). `reset` starts a new epoch: the state after a reset
depends only on the steps after it (`Silmaril.Wasi.Consequence.epochState_append_reset`).
`Policy.Hom` relates policies (`list → finset`, `list → count`); relations transport along them.
No structural rule (weakening, exchange, contraction, cut) is assumed of any reading: a component
may answer differently for permuted or duplicated assumptions, and the theorems that move between
policies take structural closure of the **target** as a hypothesis.

New definitions (no source). The SZS statuses are `Silmaril.Logic.Szs` (`szs-success`;
`szs-2007` for the 2007 text).
-/

@[expose] public section

namespace Silmaril.Wasi.Consequence

universe u v w u₁ u₂

open Silmaril.Games Silmaril.Wasi.Accept Silmaril.Logic
open Silmaril.Wasm.Component (Val)

/-! ## Observation boundaries -/

/-- The answer of a completed `check` query, read off its result. -/
inductive Answer where
  /-- Returned `true`. -/
  | yes
  /-- Returned `false`: a successful negative answer. -/
  | no
  /-- Trapped. -/
  | trap
  /-- Returned something other than one `bool`. -/
  | other
  deriving DecidableEq, Repr

/-- The answer of a result (`none`: a trap). -/
def Answer.ofResult : Option (List Val) → Answer
  | some [.bool true] => .yes
  | some [.bool false] => .no
  | none => .trap
  | some _ => .other

/-- Where an assumption, a reset or an import claim is observed. -/
inductive Boundary where
  /-- At the request (`WEv.call` for an export, `WEv.req` for an import). -/
  | call
  /-- At its answer, when that answer is not a trap (`WEv.ret … (some _)`,
  `WEv.imp … (some _)`). -/
  | answer
  deriving DecidableEq, Repr

/-- Two arguments, decoded by `d₁` and `d₂`. -/
def args2 {α β : Type} (d₁ : Val → Option α) (d₂ : Val → Option β) :
    List Val → Option (α × β)
  | [a, b] => do return (← d₁ a, ← d₂ b)
  | _ => none

/-! ## Readings and their relations -/

/-- **A protocol reading**: what the event `e`, after the events `s`, is as a query: the
assumptions, the statement and the answer, or `none` when `e` is not a query. -/
abbrev Reading (X : Type u) (C : Type v) := List WEv → WEv → Option (X × C × Answer)

variable {X : Type u} {C : Type v}

/-- **Accepted**: some play prefix of `T` ends in a query `(x, c)` answered `yes`. -/
def Accepted (T : Set (List WEv)) (r : Reading X C) (x : X) (c : C) : Prop :=
  ∃ s e, s ++ [e] ∈ T ∧ r s e = some (x, c, .yes)

/-- **The witness of an accepted query**: a play prefix ending in it. -/
def AcceptWitness (T : Set (List WEv)) (r : Reading X C) (x : X) (c : C) : Type :=
  {p : List WEv × WEv // p.1 ++ [p.2] ∈ T ∧ r p.1 p.2 = some (x, c, .yes)}

/-- Some play prefix of `T` ends in a query `(x, c)` answered `a`. -/
def Answered (T : Set (List WEv)) (r : Reading X C) (x : X) (c : C) (a : Answer) : Prop :=
  ∃ s e, s ++ [e] ∈ T ∧ r s e = some (x, c, a)

/-- Inclusion in a target system. -/
def Sound (R target : X → C → Prop) : Prop := ∀ x c, R x c → target x c

/-- The target system is included in `R`. -/
def Complete (R target : X → C → Prop) : Prop := ∀ x c, target x c → R x c

/-! ## Execution model status -/

/-- **The execution model of the query `(x, c)` as an SZS problem.** Interpretations are
completed queries (a prefix and its last event); the models of `Ax` are the completed queries
`(x, c)` of `T`, whatever their answer; the models of `C` are those answering `yes`. -/
def execProblem (T : Set (List WEv)) (r : Reading X C) (x : X) (c : C) :
    Szs.Problem (List WEv × WEv) where
  ax := {p | p.1 ++ [p.2] ∈ T ∧ ∃ a, r p.1 p.2 = some (x, c, a)}
  conj := {p | r p.1 p.2 = some (x, c, .yes)}

/-- **The execution status**: `CAX` when no query completes, otherwise `STH` (all answer `yes`),
`SCT` (none does) or `NOC` (some do, some do not). Classical; see `classify_holds`. -/
noncomputable def classify {I : Type} (P : Szs.Problem I) : Szs.Status := by
  classical exact
    if P.ax = ∅ then .CAX
    else if P.ax ⊆ P.conj then .STH
    else if P.ax ⊆ P.conjᶜ then .SCT
    else .NOC

/-- **A status pair**: the Prop consequence (existential acceptance), and the execution-model
SZS status, which is a different thing. -/
structure StatusPair where
  /-- Some completed query answers `yes`. -/
  consequence : Prop
  /-- The SZS status of the execution model (current ontology). -/
  exec : Szs.Status

/-- The status pair of the query `(x, c)`. -/
noncomputable def status (T : Set (List WEv)) (r : Reading X C) (x : X) (c : C) : StatusPair :=
  ⟨Accepted T r x c, classify (execProblem T r x c)⟩

/-! ## Hosts and environments -/

/-- A deterministic host: the answer of every import call. -/
abbrev HostFn := FnName → List Val → Option (List Val)

/-- The traces whose import answers are those of the host `h`. -/
def hostAdmissible (h : HostFn) : Set (List WEv) :=
  {t | ∀ f args res, WEv.imp f args res ∈ t → res = h f args}

/-- Accepted under every deterministic host of the class `H` (vacuous when `H` is empty). -/
def ForallHosts (H : Set HostFn) (T : Set (List WEv)) (r : Reading X C) (x : X) (c : C) : Prop :=
  ∀ h ∈ H, Accepted (T ∩ hostAdmissible h) r x c

/-- Accepted under some deterministic host of the class `H`. -/
def ExistsHost (H : Set HostFn) (T : Set (List WEv)) (r : Reading X C) (x : X) (c : C) : Prop :=
  ∃ h ∈ H, Accepted (T ∩ hostAdmissible h) r x c

/-! ## State: steps, policies and epochs -/

/-- An observed state change. -/
inductive Step (A : Type u) where
  /-- An assumption. -/
  | add (a : A)
  /-- A reset: a new epoch. -/
  | reset
  deriving DecidableEq, Repr

/-- **An update policy**: the initial state and how an assumption updates it. -/
structure Policy (A : Type u) (S : Type v) where
  init : S
  add : S → A → S

namespace Policy

variable {A : Type u}

/-- Append, in order, keeping duplicates. -/
def list : Policy A (List A) := ⟨[], fun s a => s ++ [a]⟩

/-- Insert into a finite set. -/
def finset [DecidableEq A] : Policy A (Finset A) := ⟨∅, fun s a => insert a s⟩

/-- Count the assumptions. -/
def count : Policy A Nat := ⟨0, fun n _ => n + 1⟩

/-- Keyed assumptions, the last write winning. -/
def named {K : Type u} {V : Type v} [DecidableEq K] : Policy (K × V) (K → Option V) :=
  ⟨fun _ => none, fun s p => Function.update s p.1 (some p.2)⟩

/-- Keyed assumptions, the first write winning. -/
def namedFirst {K : Type u} {V : Type v} [DecidableEq K] : Policy (K × V) (K → Option V) :=
  ⟨fun _ => none, fun s p => if s p.1 = none then Function.update s p.1 (some p.2) else s⟩

/-- **A policy morphism**: a map of states commuting with the initial state and updates. -/
structure Hom {S : Type v} {S' : Type w} (P : Policy A S) (Q : Policy A S') where
  toFun : S → S'
  map_init : toFun P.init = Q.init
  map_add : ∀ s a, toFun (P.add s a) = Q.add (toFun s) a

/-- One step: an assumption updates the state, a reset restarts from `init`. -/
def apply {S : Type v} (P : Policy A S) (s : S) : Step A → S
  | .add a => P.add s a
  | .reset => P.init

end Policy

variable {A : Type u₁} {S : Type u₂}

/-- **The state of the current epoch**: the steps folded by `P`, a reset restarting from
`P.init`. -/
def epochState (P : Policy A S) (l : List (Step A)) : S :=
  l.foldl P.apply P.init

/-- Lists to finite sets. -/
def Policy.listToFinset [DecidableEq A] : (Policy.list (A := A)).Hom Policy.finset where
  toFun := List.toFinset
  map_init := rfl
  map_add s a := by
    ext b; simp [Policy.list, Policy.finset]

/-- Lists to their length. -/
def Policy.listToCount : (Policy.list (A := A)).Hom Policy.count where
  toFun := List.length
  map_init := rfl
  map_add s a := by simp [Policy.list, Policy.count]

/-- Lists of keyed assumptions to the last write. -/
def Policy.listToNamed {K : Type u} {V : Type v} [DecidableEq K] :
    (Policy.list (A := K × V)).Hom Policy.named where
  toFun l := l.foldl Policy.named.add Policy.named.init
  map_init := rfl
  map_add s a := by simp [Policy.list, List.foldl_append]

/-- The number of resets: the index of the current epoch. -/
def epoch (l : List (Step A)) : Nat := l.countP fun | .reset => true | .add _ => false

/-! ## The four protocols as readings -/

/-- The functions of a stateful protocol. -/
structure StatefulFns where
  /-- `axiom(v)` (export) or `assume(v)` (import). -/
  add : FnName
  /-- `check(stmt) -> bool` (export) or `assert(stmt)` (import). -/
  claim : FnName
  /-- `reset()`, when the protocol has one. -/
  reset : Option FnName := none

/-- **Protocol 1: exported `check(ax, stmt) -> bool`.** A return of `f` whose arguments decode
to `(x, c)`, with its answer. -/
def exportCheck (f : FnName) (dec : List Val → Option (X × C)) : Reading X C := fun _ e =>
  match e with
  | .ret g args res => if g = f then (dec args).map fun p => (p.1, p.2, .ofResult res) else none
  | _ => none

/-- **Protocol 3: imported `assert(ax, stmt)`.** At `.call`, a call of `f` whose arguments decode
to `(x, c)`, answered `yes`; at `.answer`, the host's answer to it: `yes` when it does not trap,
`trap` when it does. -/
def importAssert (b : Boundary) (f : FnName) (dec : List Val → Option (X × C)) : Reading X C :=
  fun _ e =>
  match b, e with
  | .call, .req g args => if g = f then (dec args).map fun p => (p.1, p.2, .yes) else none
  | .answer, .imp g args res =>
    if g = f then (dec args).map fun p => (p.1, p.2, if res.isSome then .yes else .trap)
    else none
  | _, _ => none

/-- A reset event of a stateful export protocol, at the boundary `b`. -/
def isResetEv (b : Boundary) (exp : Bool) (r : FnName) : WEv → Bool
  | .call g [] => exp && b == .call && g == r
  | .ret g [] (some _) => exp && b == .answer && g == r
  | .req g [] => !exp && b == .call && g == r
  | .imp g [] (some _) => !exp && b == .answer && g == r
  | _ => false

/-- The assumption argument of an event at the boundary `b`: `exp` selects export events
(`call`/`ret`) or import events (`req`/`imp`). -/
def addArgs (b : Boundary) (exp : Bool) (f : FnName) : WEv → Option (List Val)
  | .call g args => if exp && b == .call && g == f then some args else none
  | .ret g args (some _) => if exp && b == .answer && g == f then some args else none
  | .req g args => if !exp && b == .call && g == f then some args else none
  | .imp g args (some _) => if !exp && b == .answer && g == f then some args else none
  | _ => none

/-- The observed state change of an event, assumptions decoded by `dec`. -/
def step (b : Boundary) (exp : Bool) (fns : StatefulFns) (dec : List Val → Option A) (e : WEv) :
    Option (Step A) :=
  match fns.reset with
  | some r =>
    if isResetEv b exp r e then some .reset else ((addArgs b exp fns.add e).bind dec).map .add
  | none => ((addArgs b exp fns.add e).bind dec).map .add

/-- A stateful reading: the claim of `claim`, with the state of the current epoch of the prefix. -/
def stateful (P : Policy A S) (stepOf : WEv → Option (Step A))
    (claim : WEv → Option (C × Answer)) : Reading S C := fun s e =>
  (claim e).map fun p => (epochState P (s.filterMap stepOf), p.1, p.2)

/-- **Protocol 2: exported `axiom(v)` / `check(stmt) -> bool`, optional `reset()`.** Assumptions
and resets observed at `b`, the check at its return. -/
def exportStateful (b : Boundary) (fns : StatefulFns) (P : Policy A S)
    (decA : List Val → Option A) (decC : List Val → Option C) : Reading S C :=
  stateful P (step b true fns decA) fun e =>
    match e with
    | .ret g args res => if g = fns.claim then (decC args).map (·, .ofResult res) else none
    | _ => none

/-- **Protocol 4: imported `assume(v)` / `assert(stmt)`, optional `reset()`.** Everything at
`b`; an `assert` at `.answer` whose host traps is answered `trap`. -/
def importStateful (b : Boundary) (fns : StatefulFns) (P : Policy A S)
    (decA : List Val → Option A) (decC : List Val → Option C) : Reading S C :=
  stateful P (step b false fns decA) fun e =>
    match b, e with
    | .call, .req g args => if g = fns.claim then (decC args).map (·, .yes) else none
    | .answer, .imp g args res =>
      if g = fns.claim then (decC args).map (·, if res.isSome then .yes else .trap) else none
    | _, _ => none

end Silmaril.Wasi.Consequence
