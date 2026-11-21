module

public import Silmaril.Wasm.Game.HandleAccept.Checkers.Defs

/-!
# Non-trapping read policies at Wasm: typed errors and arbitrary answers

The cons reader API (`Silmaril.Wasm.Game.HandleAccept.ConsImports`: `kind`, `car`, `cdr`,
`word`, `accept`) with **typed error answers**: an invalid query may return the code `-1`
instead of trapping.

* `kind(h) -> i32` answers `0` nil, `1` atom, `2` cons, and `-1` for an error; `kindAns (-1)`
  is the ill-typed answer `handle (-1)`, never a correct answer of a `kind` query.
* `car(h)`, `cdr(h) -> i32` answer a child handle, or `-1` for an error: the decoder
  `errDecAns` reads `-1` as the ill-typed answer `kind nil` (`carAns`), so the handle `-1` is
  reserved by the API and never names a child.

`errD` is the default answer of every query (`handle (-1)` for `kind`, `kind nil` for the
others): the reader policy `OnBadRead.dflt errD` answers invalid queries with the error code,
and `errD` is a **typed error** (`Silmaril.Accept.Handle.ErrorDisjoint`, `Thms`). Under
`OnBadRead.arbitrary` an invalid query may get any answer, error codes included.

`moduleErrLang P m ix pol oa Envs` is the reader language of a module under the read policy
`pol`; `polISpec R pol dAsk dAns ρ L` the assume/guarantee specification in which answers are
the **allowed** answers of the policy in `ρ` (`Silmaril.Accept.Handle.answers`) and `accept`
names members of `L`.

## Examples

Imports `consImports` (`0 kind`, `1 car`, `2 cdr`, `3 word`, `4 accept`), export
`check : [i32] → []`:

* `carCheck`: `c = car(h)`; return if `c = -1` (the error code); return unless `kind(c)` is
  atom; `accept(h)`. Language `carAtomL`: cons cells whose `car` is an atom.
* `carNoCheck`: the same **without** the error check.

New definitions (no source).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.ReadPolicy

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game
  Silmaril.Accept.Handle Silmaril.Formats Silmaril.Formats.Api Silmaril.Wasm.Game.HandleAccept
open Silmaril.Wasm.Logic.Strategy (ISpec)

/-- The answer of `car`/`cdr`: `-1` is the error code (the ill-typed answer `kind nil`). -/
def carAns (r : BitVec 32) : ConsA (BitVec 64) (BitVec 32) :=
  if r = -1 then .kind .nil else .handle r

/-- **The error answers**: `handle (-1)` for `kind`, `kind nil` for `atom`, `car`, `cdr`. -/
def errD : ConsQ (BitVec 32) → ConsA (BitVec 64) (BitVec 32)
  | .kind _ => .handle (-1)
  | _ => .kind .nil

variable {ts : List FnType}

/-- Answers of `kind`, `car`, `cdr` and `word`, with the error code `-1`. -/
def errDecAns (ix : ConsImports) (e : (ifaceSig ts).Op) (v : (ifaceSig ts).Ar e) :
    Option ConsEv := do
  let h ← i32Arg e.2.1
  let vs ← ansVals v
  if e.1.val = ix.kind then return .read (.kind h) (kindAns (← i32Res vs))
  else if e.1.val = ix.car then return .read (.car h) (carAns (← i32Res vs))
  else if e.1.val = ix.cdr then return .read (.cdr h) (carAns (← i32Res vs))
  else if e.1.val = ix.word then return .read (.atom h) (.atom (← i64Res vs))
  else none

/-- **The reader language of a module** with typed error answers, under the read policy
`pol`. -/
noncomputable def moduleErrLang (P : Profile) (m : Module) (ix : ConsImports)
    (pol : OnBadRead (ConsQ (BitVec 32)) (ConsA (BitVec 64) (BitVec 32))) (oa : OnInvalid)
    (Envs : Set (Env (BitVec 32) (SExp2 (BitVec 64)))) : Set (SExp2 (BitVec 64)) :=
  readerLang (consR (BitVec 64) (BitVec 32)) pol oa Envs
    (handleTraces ((Verify.instOf m).strategy P (Verify.instOf m).store) (some .enter)
      (consDecAsk ix) (errDecAns ix))

/-- **The assume/guarantee specification of a reader under a read policy** in the fixed
environment `ρ`: answers are allowed by the policy; `accept` names a member of `L`. -/
def polISpec {E : Sig.{0}} {Q A H X : Type} (R : Reader Q A H X) (pol : OnBadRead Q A)
    (dAsk : E.Op → Option (REv Q A H)) (dAns : (e : E.Op) → E.Ar e → Option (REv Q A H))
    (ρ : Env H X) (L : Set X) : ISpec E where
  pre e := ∀ h, dAsk e = some (.accept h) → ∀ t, ρ h = some t → t ∈ L
  post e v := ∀ q a, dAns e v = some (.read q a) → ∃ S, answers R pol ρ q = some S ∧ a ∈ S

end Silmaril.Wasm.Game.HandleAccept.ReadPolicy

namespace Silmaril.Wasm.Game.HandleAccept.ReadPolicy

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Formats
  Silmaril.Wasm.Game.HandleAccept.Checkers

/-- A checker module with the cons reader imports and one local. -/
def carModule (body : List Instr) : Module where
  types := [tyQ, tyW, tyA]
  imports := consImports
  funcs := [⟨⟨2⟩, [.i32], body⟩]
  exports := [⟨"check", .func ⟨5⟩⟩]

/-- `c = car(h)` into local `1`. -/
def carHead : List Instr := [.localGet ⟨0⟩, .call ⟨1⟩, .localSet ⟨1⟩]

/-- Return if `c` is the error code `-1`. -/
def errCheck : List Instr :=
  [.localGet ⟨1⟩, .intConst .i32 (-1), .intRelOp .i32 .ne, .intTestOp .i32 .eqz,
   .if_ .empty [.return_] []]

/-- Return unless `kind(c)` is atom, then `accept(h)`. -/
def carTail : List Instr :=
  [.localGet ⟨1⟩, .call ⟨0⟩, .intConst .i32 1, .intRelOp .i32 .ne, .if_ .empty [.return_] [],
   .localGet ⟨0⟩, .call ⟨4⟩]

/-- **Cons cells with an atom `car`, checking the error code.** -/
def carCheck : Module := carModule (carHead ++ errCheck ++ carTail)

/-- **The same without the error check.** -/
def carNoCheck : Module := carModule (carHead ++ carTail)

/-- Cons cells whose `car` is an atom. -/
def carAtomL : Set (SExp2 (BitVec 64)) := {t | ∃ w y, t = .cons (.atom w) y}

end Silmaril.Wasm.Game.HandleAccept.ReadPolicy
