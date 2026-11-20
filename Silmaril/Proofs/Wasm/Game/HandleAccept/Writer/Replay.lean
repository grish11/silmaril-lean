module

public import Silmaril.Wasm.Game.HandleAccept.Writer.Defs
public import Silmaril.Proofs.Wasm.Game.HandleAccept.Replay

/-!
# Cons writer acceptance from a replayed export call

The cons writer instance of `Silmaril.Proofs.Wasm.Game.HandleAccept.Replay` (store semantics):

* `consWAsk`, `consWAns`: the decoders `consWDecAsk`, `consWDecAns` on recorded moves
  (`consWDecAsk_eq`, `consWDecAns_eq`);
* **`mem_consWLang_of_replay`**: if the simulation `wRunB` of the decoded replay of an export
  call from the empty store (fresh handles, never `bad`) accepts `x`, and the policy's sentinel
  is `bad`, then `x` is in the module's cons writer language, for every profile admitting the
  deterministic steps of the replay interpreter.

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Writers

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Verify Silmaril.Wasm.Resource
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Game.HandleAccept
  Silmaril.Wasm.Game.HandleAccept.Writers Silmaril.Accept Silmaril.Accept.Handle
  Silmaril.Formats Silmaril.Formats.Api Silmaril.Proofs.Wasm.Game.HandleAccept.Replay
open Silmaril.Wasm.Numerics (Profile)

/-! ## Decoding recorded moves -/

/-- `consWDecAsk` on a recorded import call `h args`. -/
def consWAsk (ix : ConsWImports) (h : Nat) (args : List Val) : Option ConsWEv :=
  if h = ix.accept then (i32Arg args).map .accept
  else if ix.acceptAll = some h then some .acceptAll
  else none

/-- `consWDecAns` on a recorded answer `b` of import `h` called with `args`. -/
def consWAns (ix : ConsWImports) (h : Nat) (args : List Val) (b : Behaviour Val) :
    Option ConsWEv := do
  let r ← (bValsG b).bind i32Res
  if h = ix.word then return .write (.atom (← i64Arg args)) [] r
  else if h = ix.nil then
    if args = [] then return .write .nil [] r else none
  else if h = ix.cons then return .write .cons (← i32Pair args) r
  else none

variable {I : ScalarInstance}

theorem consWDecAsk_eq (ix : ConsWImports) (e : I.E.Op) :
    consWDecAsk ix e = consWAsk ix e.1.val e.2.1 :=
  rfl

theorem consWDecAns_eq (ix : ConsWImports) (e : I.E.Op) (v : I.E.Ar e) :
    consWDecAns ix e v =
      consWAns ix e.1.val e.2.1 (Answer.toBehaviour (ft := I.imports.get e.1) v) := by
  cases v <;> rfl

/-! ## Acceptance from a replay -/

/-- **Cons writer acceptance from a replay** (store semantics). If the simulation of the decoded
replay of the call of export `j` (candidate arguments `k`, script `sc`) from the empty store, with
fresh handles that are never `bad`, accepts `x`, and the policy's sentinel (if any) is `bad`,
then `x` is in the module's cons writer language, for every profile admitting the deterministic
steps of the replay interpreter. The simulation is decidable by kernel evaluation. -/
theorem mem_consWLang_of_replay {m : Module} (hm : (instance? m).isSome = true) {P : Profile}
    (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c')
    (ix : ConsWImports) {pol : Policy (BitVec 32)} {bad : BitVec 32 → Bool}
    (hbad : ∀ r, pol.sentinel = some r → bad r = true) (sc : Script) (fuel n : Nat)
    (j : Fin (instOf m).exports.length) (k : Nat) {x : SExp2 (BitVec 64)}
    (hrun : wRunB (consW (BitVec 64)) bad x Env.empty
      (rdecG (some .enter) (consWAsk ix) (consWAns ix) []
        (replayExport (instOf m) sc fuel n j k)) =
        some true) :
    x ∈ moduleConsWLang P m ix pol :=
  mem_writerLang_of_replay hm hP (consWDecAsk ix) (consWDecAns ix) (consWAsk ix) (consWAns ix)
    (consWDecAsk_eq ix) (consWDecAns_eq ix) (consW (BitVec 64)) hbad sc fuel n j k hrun

end Silmaril.Proofs.Wasm.Game.HandleAccept.Writers
