module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Session.Replay.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwnCheckedLang

public section

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Session.Replay

open Silmaril.Wasm.Numerics

/-- Exact accepted trees for the linked checked host, over every Core profile, initial
resource table and permitted export prefix. Other live slots do not affect the language. -/
theorem language_eq (P : Profile) (rt : RT) :
    language P rt = {tree | ∃ rep, rt 1 = some ⟨0, rep, true⟩ ∧ tree = resTree rep} :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwnCheckedLang.language_eq P rt

theorem language_singleton (P : Profile) {rt : RT} {rep : Nat}
    (entry : rt 1 = some ⟨0, rep, true⟩) : language P rt = {resTree rep} := by
  rw [language_eq, entry]
  ext tree; simp

theorem language_empty (P : Profile) {rt : RT}
    (missing : ∀ rep, rt 1 ≠ some ⟨0, rep, true⟩) : language P rt = ∅ := by
  rw [language_eq]
  ext tree; exact ⟨fun ⟨rep, entry, _⟩ => (missing rep entry).elim, False.elim⟩

end Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Session.Replay
