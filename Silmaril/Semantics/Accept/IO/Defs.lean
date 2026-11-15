module

public import Silmaril.Semantics.Accept.Rel.Defs

/-!
# Relational I/O acceptance: inputs that trigger outputs within a scope

A program that reads inputs and writes outputs accepts a *relation*: the pairs `(a, b)` such
that input `a` *triggers* output `b`. Two events that merely occur in the same trace are not
related causally: an output may belong to another invocation that happens to be interleaved,
to a nested (reentrant) call, or may have been produced before the input was read. This file
makes "triggers" precise by **scopes**: every observable event is tagged with the scope `k`
(an invocation or call ID) it belongs to, and only events of the same scope are related.

## Events

`Ev K X I O C` is a role-decoded event of scope `k : K`:

* `enter k x`: scope `k` opens, as the invocation of an entry point (an exported function)
  with argument `x`; `x = none` is an entry point that is not observed (its scope still owns
  its events, so they are not attributed to anything else);
* `inp k i`: an input occurrence `i` in scope `k` (for example a call of an imported
  `input()` answered with `i`, or an imported `input(i)` call: the decoder chooses);
* `out k o`: an output occurrence `o` in scope `k` (for example a call of an imported
  `output(o)`);
* `exit k c`: scope `k` ends; `c = some r` is a successful return with the value `r`,
  `c = none` an end without a successful observed result (a trap, an abort, an undecoded
  return).

Which raw events are inputs, outputs, entries and exits, and which scope they belong to, is the
job of a *decoder*. The decoder is a parameter: nothing here assumes a call direction. Import
roles (`inp`, `out`) and entry roles (`enter`, `exit`) are distinct constructors, so the
direction of each call is part of the decoded data. `bracket` assigns scope IDs to the tags of a
**well-bracketed** trace by a stack (nested and reentrant calls get their own scopes); traces
with asynchronous or overlapping calls need a decoder that supplies call IDs itself and can
use `Ev` directly.

## Runs

The local view `localView k t` keeps the events of scope `k` (`Ev.at k`). A **run** is the
causal unit read off a local view: an input, the outputs it triggers in order, and how the run
ended (`Run.result`: `some c` for a successful return of `c`, `none` otherwise). There are two
readings:

* **Input windows** (`windows`, `inputRuns`): every input occurrence `inp i` of a scope starts a
  run; its outputs are those of the same scope after it, up to the next input or the scope's
  exit; its result is the scope's return value if the scope exits before another input. Outputs
  of a scope before its first input, and events after its exit, trigger nothing.
* **Entry runs** (`entryRun`, `entryRuns`): the argument `x` of an observed entry is the input;
  the outputs are all outputs of the scope up to its exit; the result is the return value. This
  is the classic reading of an exported function `f(x) -> c` (`returns` below).

Runs that never end (a non-returning or cut-off scope) are runs with result `none`.

## Relations of a set of runs

For `S : Set (Run I O C)`:

* `triggers S : I -|> O`: `(a, b)` when some run with input `a` outputs `b`; *every* output
  occurrence of every run contributes, returned or not;
* `episodes S : I -|> List O × C`: `(a, (bs, c))` when a run with input `a` produced exactly the
  outputs `bs`, in order, and then returned `c`;
* `retTriggers S : Set (I × O × C)`: `(a, b, c)` when `b` is one of the outputs of such an
  episode (the projection of `episodes` to single outputs);
* `returns S : I -|> C`: `(a, c)` when a run with input `a` returned `c` (the classic
  input/return relation, forgetting outputs).

Successful-value projections (`Option`, `Result`-like return types) are relations composed with
a partial function, `SetRel.comp R (ofPartial f)`.

## Trace models

A trace model is a set `T` of traces of events; `inputRunsOf T` and `entryRunsOf T` are the
runs of its traces. `ScopeViews T` is the set of local views; every relation above depends on
`T` only through it (`Thms`), so traces that differ by interleaving events of different scopes
are not distinguished.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Accept.IO

open scoped Silmaril.Accept

universe u₁ u₂ u₃ u₄ u₅

/-! ## Events -/

/-- A role-decoded event of the scope `k`. -/
inductive Ev (K : Type u₁) (X : Type u₂) (I : Type u₃) (O : Type u₄) (C : Type u₅) where
  /-- Scope `k` opens: an entry point is invoked with the argument `x` (`none`: unobserved). -/
  | enter (k : K) (x : Option X)
  /-- An input occurrence in scope `k`. -/
  | inp (k : K) (i : I)
  /-- An output occurrence in scope `k`. -/
  | out (k : K) (o : O)
  /-- Scope `k` ends: `some c` returned `c`; `none` ended without a successful result. -/
  | exit (k : K) (c : Option C)
  deriving DecidableEq, Repr

/-- An event of one scope, without its scope ID. -/
inductive Loc (X : Type u₂) (I : Type u₃) (O : Type u₄) (C : Type u₅) where
  /-- The scope opens as an entry point with argument `x`. -/
  | enter (x : Option X)
  /-- An input occurrence. -/
  | inp (i : I)
  /-- An output occurrence. -/
  | out (o : O)
  /-- The scope ends. -/
  | exit (c : Option C)
  deriving DecidableEq, Repr

variable {K : Type u₁} {X : Type u₂} {I : Type u₃} {O : Type u₄} {C : Type u₅}

namespace Ev

/-- The scope of an event. -/
def scope : Ev K X I O C → K
  | enter k _ | inp k _ | out k _ | exit k _ => k

/-- The event without its scope. -/
def loc : Ev K X I O C → Loc X I O C
  | enter _ x => .enter x
  | inp _ i => .inp i
  | out _ o => .out o
  | exit _ c => .exit c

/-- The local event of scope `k`, if the event belongs to it. -/
def «at» [DecidableEq K] (k : K) (e : Ev K X I O C) : Option (Loc X I O C) :=
  if e.scope = k then some e.loc else none

end Ev

namespace Loc

/-- The scope ends here. -/
def IsExit : Loc X I O C → Prop
  | exit _ => True
  | _ => False

instance : DecidablePred (IsExit : Loc X I O C → Prop) := fun e => by
  cases e <;> simp only [IsExit] <;> infer_instance

end Loc

/-- The events of scope `k` in the trace `t`, in order. -/
def localView [DecidableEq K] (k : K) (t : List (Ev K X I O C)) : List (Loc X I O C) :=
  t.filterMap (Ev.at k)

/-- The scopes that occur in a trace, without repetition. -/
def scopes [DecidableEq K] (t : List (Ev K X I O C)) : List K :=
  (t.map Ev.scope).eraseDups

/-! ## Runs -/

/-- A run: an input, the outputs it triggered in order, and its result (`some c`: returned
`c`; `none`: no successful return, such as a trap or a scope that did not end). -/
structure Run (I : Type u₃) (O : Type u₄) (C : Type u₅) where
  /-- The input that started the run. -/
  input : I
  /-- The outputs of the run, in order. -/
  outputs : List O
  /-- How the run ended. -/
  result : Option C
  deriving DecidableEq, Repr

/-- The outputs of a local view and how it ends, up to its exit. With `stop = true` the scan
also stops at the next input (an input window); with `stop = false` it continues past inputs
(the whole scope). A view that ends without an exit has result `none`. -/
def collect (stop : Bool) : List (Loc X I O C) → List O × Option C
  | [] => ([], none)
  | .out o :: l => (o :: (collect stop l).1, (collect stop l).2)
  | .exit c :: _ => ([], c)
  | .inp _ :: l => if stop then ([], none) else collect stop l
  | .enter _ :: l => collect stop l

/-- The input windows of a local view: one run per input occurrence before the exit. -/
def windows : List (Loc X I O C) → List (Run I O C)
  | [] => []
  | .inp i :: l => ⟨i, (collect true l).1, (collect true l).2⟩ :: windows l
  | .exit _ :: _ => []
  | .out _ :: l => windows l
  | .enter _ :: l => windows l

/-- The entry run of a local view that opens with an observed entry `enter (some x)`. -/
def entryRun : List (Loc X I O C) → Option (Run X O C)
  | .enter (some x) :: l => some ⟨x, (collect false l).1, (collect false l).2⟩
  | _ => none

/-- The input-window runs of a trace, over all its scopes. -/
def inputRuns [DecidableEq K] (t : List (Ev K X I O C)) : List (Run I O C) :=
  (scopes t).flatMap fun k => windows (localView k t)

/-- The entry runs of a trace, over all its scopes. -/
def entryRuns [DecidableEq K] (t : List (Ev K X I O C)) : List (Run X O C) :=
  (scopes t).filterMap fun k => entryRun (localView k t)

/-- The local views of the traces of a trace model, over every scope. -/
def ScopeViews [DecidableEq K] (T : Set (List (Ev K X I O C))) : Set (List (Loc X I O C)) :=
  {l | ∃ t ∈ T, ∃ k, l = localView k t}

/-- The input-window runs of a trace model. -/
def inputRunsOf [DecidableEq K] (T : Set (List (Ev K X I O C))) : Set (Run I O C) :=
  {r | ∃ t ∈ T, r ∈ inputRuns t}

/-- The entry runs of a trace model. -/
def entryRunsOf [DecidableEq K] (T : Set (List (Ev K X I O C))) : Set (Run X O C) :=
  {r | ∃ t ∈ T, r ∈ entryRuns t}

/-! ## Relations of a set of runs -/

/-- **(1) Triggering**: `a` triggers `b` when some run with input `a` outputs `b`. Every output
occurrence contributes, whether or not the run returned. -/
def triggers (S : Set (Run I O C)) : I -|> O :=
  {p | ∃ r ∈ S, r.input = p.1 ∧ p.2 ∈ r.outputs}

/-- **(2) Episodes**: `a` produced exactly the outputs `bs`, in order, and then returned `c`. -/
def episodes (S : Set (Run I O C)) : I -|> List O × C :=
  {p | ⟨p.1, p.2.1, some p.2.2⟩ ∈ S}

/-- **(3) Returned triggering**: `b` is an output of an episode of `a` that returned `c`. -/
def retTriggers (S : Set (Run I O C)) : Set (I × O × C) :=
  {p | ∃ bs, (p.1, (bs, p.2.2)) ∈ episodes S ∧ p.2.1 ∈ bs}

/-- **(4) Returns**: a run with input `a` returned `c` (outputs forgotten). -/
def returns (S : Set (Run I O C)) : I -|> C :=
  {p | ∃ bs, (p.1, (bs, p.2)) ∈ episodes S}

/-- Rename the components of a run. -/
def Run.map {I' : Type*} {O' : Type*} {C' : Type*} (f : I → I') (g : O → O') (h : C → C')
    (r : Run I O C) : Run I' O' C' :=
  ⟨f r.input, r.outputs.map g, r.result.map h⟩

/-! ## Scope assignment for well-bracketed traces -/

/-- A role tag of a raw event, before scope IDs are assigned. -/
inductive Tag (X : Type u₂) (I : Type u₃) (O : Type u₄) (C : Type u₅) where
  /-- A new scope opens (an entry point is invoked; `none`: unobserved). -/
  | enter (x : Option X)
  /-- An input occurrence in the innermost open scope. -/
  | inp (i : I)
  /-- An output occurrence in the innermost open scope. -/
  | out (o : O)
  /-- The innermost open scope ends. -/
  | exit (c : Option C)
  deriving DecidableEq, Repr

/-- Assign scope IDs with a stack of open scopes: a scope's ID is the position of its `enter`
in the tag list (`n` counts tags). Inputs and outputs belong to the innermost open scope; with
no open scope they are dropped (events outside any invocation, such as start-up code), and so
is an unmatched `exit`. -/
def assign : List ℕ → ℕ → List (Tag X I O C) → List (Ev ℕ X I O C)
  | _, _, [] => []
  | st, n, .enter x :: ts => .enter n x :: assign (n :: st) (n + 1) ts
  | k :: st, n, .inp i :: ts => .inp k i :: assign (k :: st) (n + 1) ts
  | k :: st, n, .out o :: ts => .out k o :: assign (k :: st) (n + 1) ts
  | k :: st, n, .exit c :: ts => .exit k c :: assign st (n + 1) ts
  | [], n, _ :: ts => assign [] (n + 1) ts

/-- The scoped events of a well-bracketed tag list. -/
def bracket (ts : List (Tag X I O C)) : List (Ev ℕ X I O C) := assign [] 0 ts

/-- Decode a raw trace: tag each raw event by its role (`dec`; `none`: not observed) and assign
scopes. The decoder must tag every event that opens or closes a scope, even of entry points
that are not observed (`enter none`), or nesting is lost. -/
def decode {E : Type*} (dec : E → Option (Tag X I O C)) (t : List E) : List (Ev ℕ X I O C) :=
  bracket (t.filterMap dec)

end Silmaril.Accept.IO
