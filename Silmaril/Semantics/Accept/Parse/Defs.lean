module

public import Silmaril.Semantics.Accept.Handle.Defs

/-!
# Parsing sessions: input/tree relations through handle-returning exports

A *parser* module relates **input values** to **trees**. The environment feeds input through
exports and the module answers with a handle, resolved in a handle environment `ρ`
(`Silmaril.Semantics.Accept.Handle.Env`; quantified explicitly, `parseRel … Envs`). Three
export shapes, uniformly for any value type `V` and tree type `X` (S-expressions, dotted
S-expressions, tagged ASTs):

* **one-shot** `parse(data : V) -> i32` (`PEv.parse v h`): accepts the pair `([v], ρ h)`; the
  input is embedded as a singleton list so that every shape relates `List V` to `X`
  (`oneShotRel` reads the pairs back as `V × X`);
* **append/done** `append(data : V)`, `done() -> i32` (`PEv.append v`, `PEv.done h`): accepts
  `(vs, ρ h)` for the values `vs` appended since the session started;
* **chunked with a cursor** `append(chunk : list<V>)`, `done() -> (used : i32, tree : i32)`
  (`PEv.feed chunk`, `PEv.finish used h`): the input accepted is exactly the `used` values
  after the current cursor; the cursor then advances by `used`, and the unconsumed suffix stays
  buffered for the next `done`. On failure (`tree` is the sentinel) the cursor still advances
  but no pair is accepted.

## Policies (`PPolicy`)

* `sentinel`: the failure result (`0` or `-1` for `i32`). A failed `done`/`parse` accepts nothing.
* `onBadHandle`: a non-sentinel result that `ρ` does not resolve, by
  `Silmaril.Semantics.Accept.Handle.OnInvalid`. Here **every handle-returning event is itself an
  export call** (`parse`, `done`, `finish`), and its returned handle is the last thing that call
  does, so no event of the same call can follow it:
  - `callTrap` (the default, Wasm-facing): the trapped call returns nothing, i.e. it relates no
    pair; the session continues with the next export call. The environment's buffers move as for
    an answered call (`Returns`): the input handed over before the trap is not given back. As no
    event of the call follows the return, this coincides with `ignore`;
  - `sessionTrap`: the whole session is aborted (phase `dead`);
  - `ignore`: the call is answered and relates nothing;
  - `ub`: undefined behaviour.
* `onOverrun`: `used` larger than the buffered input. `callTrap` (the default) and `ignore`: the
  `done` call relates nothing and leaves the cursor; `sessionTrap`: no answer at all (the event
  is not allowed, so nothing follows); `ub`: undefined behaviour. The cursor invariant counts the
  `used` of every chunked `done`, so it is stated for `sessionTrap` (`Thms.run_cursor`).
* `doneClears`: whether `done()` starts a new session (`true`: the append buffer is cleared; a
  second `done()` relates the empty input) or keeps accumulating (`false`: the next `done`
  relates every value appended since the last `reset`).
* `reset()` (`PEv.reset`) clears both buffers. Extensions (several sessions, explicit session
  handles) are further event constructors with their own responses.

The `used` result is an `i32`; `usedOfI32` reads it as an unsigned count when its sign bit is
clear and as an overrun otherwise, so one `done` consumes at most `2 ^ 31 - 1` values even when
more are buffered (`usedOfI32_lt`).

## Projections

`parseRel pol Envs T : Set (List V × X)` is the relation of a set of module traces. Forgetting
the tree gives its **input language** `inputLang`, forgetting the input its **tree language**
`treeLang`. Both are images, so they preserve unions but not intersections (`Thms`,
`Examples`).

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Accept.Parse

open Silmaril.Accept.Handle

universe u v w

/-- Parsing-session events. -/
inductive PEv (V : Type u) (H : Type v) where
  | parse (v : V) (h : H)
  | append (v : V)
  | done (h : H)
  | feed (chunk : List V)
  | finish (used : Nat) (h : H)
  | reset

/-- Parsing-session policies. -/
structure PPolicy (H : Type v) where
  sentinel : H
  onBadHandle : OnInvalid := .callTrap
  onOverrun : OnInvalid := .callTrap
  doneClears : Bool := true

/-- The environment state: the append buffer, the chunk buffer (from the cursor on) and the
phase. -/
structure PState (V : Type u) where
  acc : List V
  buf : List V
  phase : Phase

def PState.init {V : Type u} : PState V := ⟨[], [], .live⟩

variable {V : Type u} {H : Type v} {X : Type w}

/-- What a returned handle accepts: nothing for the sentinel, the pair for a resolved handle;
`none` for an unresolved handle (handled by `onBadHandle`). -/
def resolve [DecidableEq H] (pol : PPolicy H) (ρ : Env H X) (w : List V) (h : H) :
    Option (Set (List V × X)) :=
  if h = pol.sentinel then some ∅ else (ρ h).map fun x => {(w, x)}

/-- The handle-returning calls: the input `w` they relate, the returned handle and the state
after them (`finish` requires `used` within the buffered input). -/
def Returns (pol : PPolicy H) : PState V → PEv V H → List V → H → PState V → Prop
  | s, .parse v h, w, h', s' => w = [v] ∧ h' = h ∧ s' = s
  | s, .done h, w, h', s' => w = s.acc ∧ h' = h ∧
      s' = ⟨if pol.doneClears then [] else s.acc, s.buf, s.phase⟩
  | s, .finish n h, w, h', s' => n ≤ s.buf.length ∧ w = s.buf.take n ∧ h' = h ∧
      s' = ⟨s.acc, s.buf.drop n, s.phase⟩
  | _, _, _, _, _ => False

/-- **The parsing response relation** in the environment `ρ`. A handle-returning call moves
to the state given by `Returns`; an unresolved handle then follows `onBadHandle` (a call-local
trap of a handle-returning call is that call relating nothing, `retBadIgnore`). -/
inductive PStep [DecidableEq H] (pol : PPolicy H) (ρ : Env H X) :
    PState V → PEv V H → PState V → Set (List V × X) → Prop where
  | ret {s s' : PState V} {e : PEv V H} {w : List V} {h : H} {A : Set (List V × X)} :
      s.phase = .live → Returns pol s e w h s' → resolve pol ρ w h = some A →
      PStep pol ρ s e s' A
  | retBadIgnore {s s' : PState V} {e : PEv V H} {w : List V} {h : H} :
      s.phase = .live → Returns pol s e w h s' → resolve pol ρ w h = none →
      (pol.onBadHandle = .ignore ∨ pol.onBadHandle = .callTrap) → PStep pol ρ s e s' ∅
  | retBadSessionTrap {s s' : PState V} {e : PEv V H} {w : List V} {h : H} :
      s.phase = .live → Returns pol s e w h s' → resolve pol ρ w h = none →
      pol.onBadHandle = .sessionTrap → PStep pol ρ s e {s' with phase := .dead} ∅
  | retBadUB {s s' : PState V} {e : PEv V H} {w : List V} {h : H} :
      s.phase = .live → Returns pol s e w h s' → resolve pol ρ w h = none →
      pol.onBadHandle = .ub → PStep pol ρ s e {s' with phase := .chaos} Set.univ
  | append {acc buf : List V} (v : V) :
      PStep pol ρ ⟨acc, buf, .live⟩ (.append v) ⟨acc ++ [v], buf, .live⟩ ∅
  | feed {acc buf : List V} (chunk : List V) :
      PStep pol ρ ⟨acc, buf, .live⟩ (.feed chunk) ⟨acc, buf ++ chunk, .live⟩ ∅
  | overrunIgnore {acc buf : List V} {n : Nat} {h : H} :
      buf.length < n → (pol.onOverrun = .ignore ∨ pol.onOverrun = .callTrap) →
      PStep pol ρ ⟨acc, buf, .live⟩ (.finish n h) ⟨acc, buf, .live⟩ ∅
  | overrunUB {acc buf : List V} {n : Nat} {h : H} :
      buf.length < n → pol.onOverrun = .ub →
      PStep pol ρ ⟨acc, buf, .live⟩ (.finish n h) ⟨acc, buf, .chaos⟩ Set.univ
  | reset {acc buf : List V} : PStep pol ρ ⟨acc, buf, .live⟩ .reset ⟨[], [], .live⟩ ∅
  | chaos {s : PState V} (e : PEv V H) :
      s.phase = .chaos → PStep pol ρ s e s Set.univ

/-- **The parsing host** of the environment `ρ`. -/
def parser [DecidableEq H] (pol : PPolicy H) (ρ : Env H X) :
    Host (PEv V H) (List V × X) (PState V) :=
  ⟨PState.init, PStep pol ρ⟩

/-- **The input/tree relation** of a set of module traces, over the environments `Envs`. -/
def parseRel [DecidableEq H] (pol : PPolicy H) (Envs : Set (Env H X))
    (T : Set (List (PEv V H))) : Set (List V × X) :=
  langOver (fun ρ : Envs => parser pol ρ.1) T

/-- The input language of a relation: forget the tree. -/
def inputLang (R : Set (List V × X)) : Set (List V) := Prod.fst '' R

/-- The tree language of a relation: forget the input. -/
def treeLang (R : Set (List V × X)) : Set X := Prod.snd '' R

/-- One-shot pairs, read back without the singleton embedding. -/
def oneShotRel (R : Set (List V × X)) : Set (V × X) := {p | ([p.1], p.2) ∈ R}

/-- The values fed through `append(chunk)` along a trace, since its start. -/
def fed : List (PEv V H) → List V
  | [] => []
  | .feed c :: es => c ++ fed es
  | _ :: es => fed es

/-- The values consumed by `done() -> (used, tree)` along a trace. -/
def consumed : List (PEv V H) → Nat
  | [] => 0
  | .finish n _ :: es => n + consumed es
  | _ :: es => consumed es

/-- A trace without `reset`. -/
def ResetFree (t : List (PEv V H)) : Prop := PEv.reset ∉ t

/-- Only chunk events: `append(chunk)` and `done() -> (used, tree)`. -/
def ChunkOnly (t : List (PEv V H)) : Prop :=
  ∀ e ∈ t, (∃ c, e = .feed c) ∨ (∃ n h, e = .finish n h)

/-- Only append/done events. -/
def AppendOnly (t : List (PEv V H)) : Prop :=
  ∀ e ∈ t, (∃ v, e = .append v) ∨ (∃ h, e = .done h)

/-- The append buffer after a trace, from `acc`: appended values since the last `done` (when
`done` clears) or since the start. -/
def pending (clears : Bool) : List V → List (PEv V H) → List V
  | acc, [] => acc
  | acc, .append v :: es => pending clears (acc ++ [v]) es
  | acc, .done _ :: es => pending clears (if clears then [] else acc) es
  | _, .reset :: es => pending clears [] es
  | acc, _ :: es => pending clears acc es

/-- The `used` count of an `i32` result: its unsigned value when the sign bit is clear. -/
def usedOfI32 (b : BitVec 32) : Option Nat := if b.msb then none else some b.toNat

end Silmaril.Accept.Parse
