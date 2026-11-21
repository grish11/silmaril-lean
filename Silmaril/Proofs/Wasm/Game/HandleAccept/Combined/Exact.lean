module

public import Silmaril.Wasm.Game.HandleAccept.Combined.Examples
import Silmaril.Proofs.Wasm.Game.HandleAccept.Combined.Replay
import Silmaril.Wasm.Resource.Replay.Kernel.Thms

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Combined

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Verify
  Silmaril.Wasm.Resource Silmaril.Formats Silmaril.Formats.Api Silmaril.Accept.Handle
  Silmaril.Wasm.Game.HandleAccept Silmaril.Wasm.Game.HandleAccept.Combined
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Proofs.Wasm.Game.HandleAccept.Replay (rdecG)
open Silmaril.Wasm.Resource.Replay.Kernel (replayFromK_eq)

private def alternateScript : Script := fun index _ _ =>
  [[Val.i32 4], [Val.i32 5], [Val.i32 6], [Val.i32 2], [Val.i32 4], [Val.i32 1], [Val.i32 5],
    [Val.i32 0], []].getD index []

private def exportIndex : Fin (instOf readBack).exports.length := ⟨0, by decide +kernel⟩

private def readBackTrace (alternate : Bool) (word : BitVec 64) : List ConsCEv :=
  let atomHandle : BitVec 32 := if alternate then 4 else 1
  let nilHandle : BitVec 32 := if alternate then 5 else 2
  let listHandle : BitVec 32 := if alternate then 6 else 3
  [.w .enter, .w (.write (.atom word) [] atomHandle), .w (.write .nil [] nilHandle),
    .w (.write .cons [atomHandle, nilHandle] listHandle), .r (.kind listHandle) (.kind .cons),
    .r (.car listHandle) (.handle atomHandle), .r (.kind atomHandle) (.kind .atom),
    .r (.cdr listHandle) (.handle nilHandle), .r (.kind nilHandle) (.kind .nil),
    .w (.accept listHandle)]

private theorem decoded (alternate : Bool) (input : Nat) :
    rdecG (some (.w .enter)) (combAsk readBackIx) (combAns readBackIx) []
      (replayExport (instOf readBack) (if alternate then alternateScript else readBackScript)
        32 10 exportIndex input) = readBackTrace alternate (BitVec.ofNat 64 input) := by
  cases alternate <;> rw [replayExport, ← replayFromK_eq] <;> kernel_rfl

private theorem accepts_input {P : Profile}
    (hP : ∀ before after : Config Nat,
      Step (profile refOracle) Det.noHost before after → Step P Det.noHost before after)
    (pol : Policy (BitVec 32)) (input : Nat) :
    SExp2.cons (.atom (BitVec.ofNat 64 input)) .nil ∈ moduleCombLang P readBack readBackIx pol := by
  by_cases first : pol.sentinel = some 1 ∨ pol.sentinel = some 2 ∨ pol.sentinel = some 3
  · have notAlternate (handle : BitVec 32) (h : handle = 4 ∨ handle = 5 ∨ handle = 6) :
        pol.sentinel ≠ some handle := by
      intro equal
      rw [equal] at first
      rcases h with rfl | rfl | rfl <;> exact (by decide +kernel : ¬ (_ = _ ∨ _ = _ ∨ _ = _)) first
    refine mem_combLang_of_replay readBack_instance hP readBackIx
      (bad := fun handle => decide (pol.sentinel = some handle)) (fun _ equal => by simp [equal])
      alternateScript 32 10 exportIndex input ?_
    rw [show alternateScript = (if true then alternateScript else readBackScript) from rfl,
      decoded true input]
    simp [readBackTrace, cRunB, consOkB, consW, Writer.built, Env.lookupAll, Env.empty,
      Function.update, consKind]
    exact ⟨notAlternate 4 (Or.inl rfl), notAlternate 5 (Or.inr (Or.inl rfl)),
      notAlternate 6 (Or.inr (Or.inr rfl))⟩
  · have notOne : pol.sentinel ≠ some 1 := fun equal => first (Or.inl equal)
    have notTwo : pol.sentinel ≠ some 2 := fun equal => first (Or.inr (Or.inl equal))
    have notThree : pol.sentinel ≠ some 3 := fun equal => first (Or.inr (Or.inr equal))
    refine mem_combLang_of_replay readBack_instance hP readBackIx
      (bad := fun handle => decide (pol.sentinel = some handle)) (fun _ equal => by simp [equal])
      readBackScript 32 10 exportIndex input ?_
    rw [show readBackScript = (if false then alternateScript else readBackScript) from rfl,
      decoded false input]
    simp [readBackTrace, cRunB, consOkB, consW, Writer.built, Env.lookupAll, Env.empty,
      Function.update, consKind]
    exact ⟨notOne, notTwo, notThree⟩

theorem readBack_exact {P : Profile}
    (hP : ∀ before after : Config Nat,
      Step (profile refOracle) Det.noHost before after → Step P Det.noHost before after)
    {pol : Policy (BitVec 32)} (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    moduleCombLang P readBack readBackIx pol = singleL := by
  refine (readBack_sound P hw ha).antisymm fun tree member => ?_
  rcases member with ⟨word, rfl⟩
  simpa using accepts_input hP pol word.toNat

end Silmaril.Proofs.Wasm.Game.HandleAccept.Combined
