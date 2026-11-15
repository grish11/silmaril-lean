module

public import Silmaril.Semantics.Accept.IO.Defs
public import Silmaril.Wasi.Component.Accept.Defs

/-! # Relational I/O acceptance of component traces

The bridge from the named traces of a component (`Silmaril.Wasi.World`: `WEv`, `wtrace`) to the
scoped runs of `Silmaril.Accept.IO`. A component `σ : Strategy (nsig Im) (nsig Ex)` imports the
functions `Im` and exports `Ex`; its named traces are `Silmaril.Wasi.Accept.Traces σ`.

## Directions and roles

The four `WEv`s have fixed directions:

| event | direction | who moves |
| --- | --- | --- |
| `call f args` | the environment calls the **export** `f` | Opponent |
| `ret f args res` | the export call returns (`some r`) or traps (`none`) | Proponent |
| `req f args` | the component calls the **import** `f` | Proponent |
| `imp f args res` | the host answers the import call (`some r`) or traps (`none`) | Opponent |

A **trap** is a `none` answer: `ret f args none` is a trap of the component in the export call,
`imp f args none` a trap reported by the host for an import call. `Roles X I O C` says which
events carry entries `X`, inputs `I`, outputs `O` and results `C`:

* `entry f args`: the export call `call f args` is an observed entry with argument `x`; `none`
  opens an *unobserved* scope (it still owns its events);
* `result f args r`: the successful return `ret f args (some r)` decodes to the result `c`;
  `none` (undecoded) and a trap `ret f args none` both close the scope with `exit none`;
* `callIn f args`: the import call `req f args` carries an input (an `input(a)`-style import);
* `answerIn f args r`: the host's answer `imp f args (some r)` carries an input (an
  `input() -> a`-style import);
* `callOut f args`: the import call `req f args` is an output (an `output(b)` import); it takes
  precedence over `callIn` on the same event.

`tag ρ` tags **every** `call` (`enter`) and **every** `ret` (`exit`), so scopes are kept even
for exports that are not observed. A host trap `imp f args none` and an import event with no
role produce no tag: they belong to no run.

## Runs of a component

* `ioRuns σ ρ`: the input-window runs (`Silmaril.Accept.IO.inputRunsOf`) of the decoded traces
  `decode (tag ρ) '' Traces σ`; `entryIORuns σ ρ`: the entry runs (`entryRunsOf`).
* `importIO inp out decI decO`: input through the answer of the import `inp`, output through
  the arguments of calls to the import `out`; every export call is an entry `()` and every
  successful return the result `()`.
* `exportFn f decX decC`: the classic reading of an export `f(x) -> c`, no inputs or outputs.

## Scopes of legal plays

Legal plays of `nsig Im ↠ nsig Ex` are single-threaded and well bracketed with depth one
(`Silmaril.Games.Play`): an export call is answered before the next one, and the component
makes import calls only while it runs an export call. The game has no callbacks from an import
into an export, so **reentrancy cannot occur** and the nesting support of `bracket` is unused.
`Shallow` is the corresponding automaton on tag lists (`Thms`: every legal play's tags are
`Shallow false`); `blocks` splits a tag list at each `enter`, and `wblocks` splits a named trace
at each export call: each block is the scope of one export call (`Thms`).

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasi.IOAccept

open Silmaril.Games Silmaril.Accept.IO
open Silmaril.Wasm.Component (Val)

/-! ## Roles -/

/-- The role decoders of a component's named events (see the module docstring). -/
structure Roles (X I O C : Type) where
  /-- An export call `call f args` observed as an entry; `none`: an unobserved scope. -/
  entry : FnName → List Val → Option X
  /-- A successful return `ret f args (some r)` decoded as a result; `none`: undecoded. -/
  result : FnName → List Val → List Val → Option C
  /-- An import call `req f args` carrying an input. -/
  callIn : FnName → List Val → Option I
  /-- A host answer `imp f args (some r)` carrying an input. -/
  answerIn : FnName → List Val → List Val → Option I
  /-- An import call `req f args` issuing an output (takes precedence over `callIn`). -/
  callOut : FnName → List Val → Option O

variable {X I O C : Type}

/-- The tag of a named event: every export call opens a scope and every export return or trap
closes one; import calls and answers are inputs or outputs by their roles; host traps
(`imp f args none`) are not tagged. -/
def tag (ρ : Roles X I O C) : WEv → Option (Tag X I O C)
  | .call f a => some (.enter (ρ.entry f a))
  | .ret f a (some r) => some (.exit (ρ.result f a r))
  | .ret _ _ none => some (.exit none)
  | .req f a =>
    match ρ.callOut f a with
    | some o => some (.out o)
    | none => (ρ.callIn f a).map .inp
  | .imp f a (some r) => (ρ.answerIn f a r).map .inp
  | .imp _ _ none => none

/-- The local (scope-free) event of a tag. -/
def tagLoc : Tag X I O C → Loc X I O C
  | .enter x => .enter x
  | .inp i => .inp i
  | .out o => .out o
  | .exit c => .exit c

/-! ## Runs of a component -/

/-- The input-window runs of a component under the roles `ρ`. -/
def ioRuns {Im Ex : Set FnName} (σ : Strategy (nsig Im) (nsig Ex)) (ρ : Roles X I O C) :
    Set (Run I O C) :=
  inputRunsOf (decode (tag ρ) '' Silmaril.Wasi.Accept.Traces σ)

/-- The entry runs of a component under the roles `ρ`. -/
def entryIORuns {Im Ex : Set FnName} (σ : Strategy (nsig Im) (nsig Ex)) (ρ : Roles X I O C) :
    Set (Run X O C) :=
  entryRunsOf (decode (tag ρ) '' Silmaril.Wasi.Accept.Traces σ)

/-- Input through the host's answer to the import `inp` (decoded by `decI`), output through the
arguments of calls to the import `out` (decoded by `decO`). Export calls are entries `()`;
successful returns are results `()`. -/
def importIO (inp out : FnName) (decI : List Val → Option I) (decO : List Val → Option O) :
    Roles Unit I O Unit where
  entry _ _ := some ()
  result _ _ _ := some ()
  callIn _ _ := none
  answerIn f _ r := if f = inp then decI r else none
  callOut f a := if f = out then decO a else none

/-- The export `f(x) -> c`: arguments decoded by `decX`, successful results by `decC`; other
exports open unobserved scopes. No inputs or outputs. -/
def exportFn (f : FnName) (decX : List Val → Option X) (decC : List Val → Option C) :
    Roles X Empty Empty C where
  entry g a := if g = f then decX a else none
  result g _ r := if g = f then decC r else none
  callIn _ _ := none
  answerIn _ _ _ := none
  callOut _ _ := none

/-! ## Scopes of single-threaded traces -/

/-- The tags of an input or output, which do not open or close a scope. -/
def IsBody : Tag X I O C → Prop
  | .inp _ | .out _ => True
  | _ => False

/-- The depth-one bracketing automaton: `Shallow false` outside a scope, `Shallow true` inside
one. Inputs and outputs occur only inside, `enter` only outside, `exit` only inside. -/
inductive Shallow : Bool → List (Tag X I O C) → Prop
  /-- The end of the list, inside or outside a scope (a last scope may stay open). -/
  | nil (b : Bool) : Shallow b []
  /-- A scope opens. -/
  | enter (x : Option X) {l : List (Tag X I O C)} : Shallow true l → Shallow false (.enter x :: l)
  /-- An input inside a scope. -/
  | inp (i : I) {l : List (Tag X I O C)} : Shallow true l → Shallow true (.inp i :: l)
  /-- An output inside a scope. -/
  | out (o : O) {l : List (Tag X I O C)} : Shallow true l → Shallow true (.out o :: l)
  /-- The scope closes. -/
  | exit (c : Option C) {l : List (Tag X I O C)} : Shallow false l → Shallow true (.exit c :: l)

/-- The local events of a tag list up to its next `enter`. -/
def seg : List (Tag X I O C) → List (Loc X I O C)
  | [] => []
  | .enter _ :: _ => []
  | t :: ts => tagLoc t :: seg ts

/-- The blocks of a tag list: each `enter` with the local events up to the next `enter`. Tags
before the first `enter` belong to no block. -/
def blocks : List (Tag X I O C) → List (List (Loc X I O C))
  | [] => []
  | .enter x :: ts => (.enter x :: seg ts) :: blocks ts
  | _ :: ts => blocks ts

/-- An export call. -/
def isCall : WEv → Bool
  | .call .. => true
  | _ => false

/-- The events of a named trace up to its next export call. -/
def wseg : List WEv → List WEv
  | [] => []
  | e :: t => if isCall e then [] else e :: wseg t

/-- The call blocks of a named trace: each export call with the events up to the next one.
Events before the first export call belong to no block. -/
def wblocks : List WEv → List (List WEv)
  | [] => []
  | e :: t => if isCall e then (e :: wseg t) :: wblocks t else wblocks t

/-- The local event of a named event under the roles `ρ`. -/
def locOf (ρ : Roles X I O C) (e : WEv) : Option (Loc X I O C) := (tag ρ e).map tagLoc

end Silmaril.Wasi.IOAccept
