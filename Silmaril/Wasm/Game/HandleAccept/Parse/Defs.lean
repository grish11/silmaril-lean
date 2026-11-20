module

public import Silmaril.Wasm.Game.HandleAccept.Writer.Defs
public import Silmaril.Semantics.Accept.Parse.Defs

/-!
# Parsing exports of core Wasm modules

A parser module is driven through its **exports**: the environment calls them with data and
the module answers with handles. The parsing events `Silmaril.Accept.Parse.PEv` are decoded from
the **export answers** `.inr (.ans f v)` of instance plays (`f = ⟨j, args⟩` carries the export
index and its arguments, `v` the module's answer); import moves and export questions are not
events (`exportEvents`). Exports, by index (`ParseExports V`, every one optional), with data
values decoded by `val` (for instance `i64Val` for `i64` data, `i32Val` for `i32` data):

* `parse(data) -> i32`: `PEv.parse v h`;
* `append(data)` (no result): `PEv.append v`;
* `done() -> i32`: `PEv.done h`;
* `feed(data)` (no result): a one-value chunk `PEv.feed [v]` (chunks of several values pass
  through memory and are not decoded here);
* `finish() -> (used : i32, tree : i32)`: `PEv.finish used h`, `used` read **unsigned**
  (`BitVec.toNat`). It agrees with the signed reading `Silmaril.Accept.Parse.usedOfI32`
  wherever that one is defined (`Thms`); a `used` with its sign bit set is a count of at least
  `2 ^ 31`, an overrun unless that much input is buffered;
* `reset()`: `PEv.reset`.

Only calls the module **returns from** with values of the expected shape are events: an export
call that traps (or throws, or diverges) is not part of the session, so in particular a trapped
`append(v)` does not add `v` to the input.

`moduleParseRel P m ix pol Envs` is the input/tree relation (`Silmaril.Accept.Parse.parseRel`)
of a module's instance over the environments `Envs`. `parseESpec ix s ρ R` is the export
specification of a one-shot parser in the fixed environment `ρ`: a `parse(v)` answer other than
the sentinel `s` names a handle whose tree `x` in `ρ` is related to `v` (`([v], x) ∈ R`).

New definitions (no source).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Parsing

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game
  Silmaril.Accept.Handle Silmaril.Accept.Parse Silmaril.Wasm.Game.HandleAccept
open Silmaril.Wasm.Logic.Strategy (ISpec)

/-! ## Decoding export moves -/

variable {E F : Sig.{0}} {Ev : Type}

/-- The decoded events of a play: export answers through `dec`; every other move is no
event. -/
def exportEvents (dec : (f : F.Op) → F.Ar f → Option Ev) : List (Move E F) → List Ev
  | [] => []
  | .inr (.ans f v) :: p => (dec f v).toList ++ exportEvents dec p
  | _ :: p => exportEvents dec p

/-- The decoded export traces of a strategy. -/
def exportTraces (σ : Strategy E F) (dec : (f : F.Op) → F.Ar f → Option Ev) : Set (List Ev) :=
  {t | ∃ p ∈ σ, t = exportEvents dec p}

/-! ## The parsing exports -/

/-- Data as one `i64` argument. -/
def i64Val : List Val → Option (BitVec 64) := Writers.i64Arg

/-- Data as one `i32` argument. -/
def i32Val : List Val → Option (BitVec 32) := i32Arg

/-- Export indices of a parsing API, with the decoding of data arguments. -/
structure ParseExports (V : Type) where
  val : List Val → Option V
  parse : Option Nat := none
  append : Option Nat := none
  done : Option Nat := none
  feed : Option Nat := none
  finish : Option Nat := none
  reset : Option Nat := none

variable {V : Type} {ts : List FnType}

/-- `(used, tree)` returned by `finish`. -/
def i32Two : List Val → Option (BitVec 32 × BitVec 32)
  | [.num ⟨.int .i32, a⟩, .num ⟨.int .i32, b⟩] => some (a, b)
  | _ => none

/-- **The parsing event of an export answer.** -/
def parseDec (ix : ParseExports V) (f : (ifaceSig ts).Op) (v : (ifaceSig ts).Ar f) :
    Option (PEv V (BitVec 32)) := do
  let vs ← ansVals v
  let j := f.1.val
  if ix.parse = some j then
    return .parse (← ix.val f.2.1) (← i32Res vs)
  else if ix.append = some j then
    if vs = [] then return .append (← ix.val f.2.1) else none
  else if ix.done = some j then
    return .done (← i32Res vs)
  else if ix.feed = some j then
    if vs = [] then return .feed [← ix.val f.2.1] else none
  else if ix.finish = some j then
    let (u, h) ← i32Two vs
    return .finish u.toNat h
  else if ix.reset = some j then
    if vs = [] then return .reset else none
  else none

/-- **The input/tree relation of a parser module** over the environments `Envs`. -/
noncomputable def moduleParseRel {X : Type} (P : Profile) (m : Module) (ix : ParseExports V)
    (pol : PPolicy (BitVec 32)) (Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) X)) :
    Set (List V × X) :=
  parseRel pol Envs
    (exportTraces ((Verify.instOf m).strategy P (Verify.instOf m).store) (parseDec ix))

/-- Only one-shot exports (`parse`, and possibly `reset`). -/
def ParseExports.OneShot (ix : ParseExports V) : Prop :=
  ix.append = none ∧ ix.done = none ∧ ix.feed = none ∧ ix.finish = none

/-- **The export specification of a one-shot parser** in the fixed environment `ρ`: a
`parse(v)` answer other than the sentinel `s` names a handle whose tree in `ρ`, if any, is
related to `v` by `R`; every export call is allowed. -/
def parseESpec {X : Type} (ix : ParseExports V) (s : BitVec 32)
    (ρ : Silmaril.Accept.Handle.Env (BitVec 32) X) (R : Set (List V × X)) :
    ISpec (ifaceSig ts) where
  pre _ := True
  post f v := ∀ w h, parseDec ix f v = some (.parse w h) → h ≠ s → ∀ x, ρ h = some x → ([w], x) ∈ R

end Silmaril.Wasm.Game.HandleAccept.Parsing
