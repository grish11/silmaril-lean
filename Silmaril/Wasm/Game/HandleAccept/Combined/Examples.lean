module

public import Silmaril.Wasm.Game.HandleAccept.Combined.Thms
public import Silmaril.Wasm.Resource.Replay.Defs
import Silmaril.Wasm.Execution.Core.SpecProfile
import Silmaril.Proofs.Wasm.Game.HandleAccept.Combined.Replay

/-!
# Combined writer and reader sessions: non-vacuity

`readBack_sound` bounds the combined language of `readBack` by `singleL`. Here it is shown
non-empty by running the module: the call `run(k)` is replayed on the verified interpreter
with a host (`readBackScript`) whose writes return the fresh handles `1` (`word`), `2` (`nil`),
`3` (`cons`) and whose reads answer from that store (`kind(3) = 2`, `car(3) = 1`,
`kind(1) = 1`, `cdr(3) = 2`, `kind(2) = 0`); the combined host is simulated along the decoded
events, with every read checked against the store **at the time of the read**
(`Silmaril.Proofs.Wasm.Game.HandleAccept.Combined.mem_combLang_of_replay`).

* `readBack_accepts_0`, `readBack_accepts_5`: `(0)` and `(5)` are in the combined language,
  for every profile admitting the interpreter's deterministic steps and every policy whose
  sentinel, if any, is `0`; `_spec` at the specification profiles.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Combined

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Verify
  Silmaril.Wasm.Resource Silmaril.Formats Silmaril.Accept.Handle

/-- The host of `readBack`: the answers of the callouts in order. -/
def readBackScript : Script := fun k _ _ =>
  [[Val.i32 1], [Val.i32 2], [Val.i32 3], [Val.i32 2], [Val.i32 1], [Val.i32 1], [Val.i32 2],
    [Val.i32 0], []].getD k []

section Positive

variable {P : Profile}
  (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c')
  {pol : Policy (BitVec 32)} (hs : ∀ r, pol.sentinel = some r → r = 0)
include hP hs

open Silmaril.Proofs.Wasm.Game.HandleAccept.Combined (mem_combLang_of_replay)

theorem readBack_accepts_0 : SExp2.cons (.atom 0) .nil ∈ moduleCombLang P readBack readBackIx pol :=
  mem_combLang_of_replay readBack_instance hP readBackIx (bad := fun r => decide (r = 0))
    (fun r h => by simp [hs r h]) readBackScript refFuel 10 ⟨0, by decide +kernel⟩ 0
    (by decide +kernel)

theorem readBack_accepts_5 : SExp2.cons (.atom 5) .nil ∈ moduleCombLang P readBack readBackIx pol :=
  mem_combLang_of_replay readBack_instance hP readBackIx (bad := fun r => decide (r = 0))
    (fun r h => by simp [hs r h]) readBackScript refFuel 10 ⟨0, by decide +kernel⟩ 5
    (by decide +kernel)

end Positive

theorem readBack_accepts_0_spec (nd : Bool) {pol : Policy (BitVec 32)}
    (hs : ∀ r, pol.sentinel = some r → r = 0) :
    SExp2.cons (.atom 0) .nil ∈ moduleCombLang (Profile.spec nd {}) readBack readBackIx pol :=
  readBack_accepts_0 (fun _ _ h => Step.deterministic_refines_spec nd h) hs

end Silmaril.Wasm.Game.HandleAccept.Combined
