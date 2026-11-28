module

import Silmaril.Wasm.Component.SyncITree.Thms
import Silmaril.Wasm.Component.Reference.Adequacy.Thms
import Silmaril.Wasm.Component.Reference.SessionAdequacy.Thms

/-! A downstream caller sees the write made by a previous call even though
that call trapped during the canonical lift. -/

namespace Silmaril.Wasm.Component.SyncITree.Regression

open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.SingleThreaded (neverFail profile)

private noncomputable def ready : Ready pokePeekS := Ready.ofAdequate pokePeekS_adequate

private def poke : Question pokePeekS := ⟨⟨0, by decide⟩, ⟨[], by decide⟩⟩
private def peek : Question pokePeekS := ⟨⟨1, by decide⟩, ⟨[], by decide⟩⟩

private theorem session : Completes neverFail ready [poke, peek] [none, some [.u32 1]] :=
  (completes_iff_reference .deterministic).mpr (witness_session neverFail .deterministic).1

example : sessMoves pokePeekS (List.map Question.erase [poke, peek]) [none, some [.u32 1]] ∈
    pokePeekS.toComp.den (modSem (profile neverFail)) :=
  (completes_iff_game rfl).mp session

example : sessMoves pokePeekS (List.map Question.erase [poke, peek]) [none, some [.u32 1]] ++
    [.inr (.ask peek.gameOp)] ∈ pokePeekS.toComp.den (modSem (profile neverFail)) :=
  (pending_iff_game rfl peek).mp session

private noncomputable def zero : Ready zeroS := Ready.ofAdequate zeroS_adequate

private def zeroPoke : Question zeroS := ⟨⟨0, by decide⟩, ⟨[], by decide⟩⟩
private def zeroPeek : Question zeroS := ⟨⟨1, by decide⟩, ⟨[], by decide⟩⟩

-- The same trap followed by a read from the component without the write
-- cannot yield the same value.
example : ¬ Completes neverFail zero [zeroPoke, zeroPeek] [none, some [.u32 1]] :=
  fun h => (witness_session neverFail .deterministic).2 ((completes_iff_reference .deterministic).mp h)

-- A value of the wrong arity cannot be used to construct the typed question.
example : ValTy.checkList pokePeekS.exports[peek.exportIdx].ty.params [.u32 7] = false := by
  decide

end Silmaril.Wasm.Component.SyncITree.Regression
