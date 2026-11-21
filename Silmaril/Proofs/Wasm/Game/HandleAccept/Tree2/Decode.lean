module

public import Silmaril.Wasm.Game.HandleAccept.Tree2.Defs

/-! # Proofs: what the binary-tree writer decoders produce

New proofs (no source). -/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Tree2

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game
  Silmaril.Wasm.Game.HandleAccept Silmaril.Wasm.Game.HandleAccept.Writers
  Silmaril.Wasm.Game.HandleAccept.Tree2 Silmaril.Accept.Handle Silmaril.Formats.Api

variable {ts : List FnType}

theorem pairWDecAns_cases {ix : PairWImports} {e : (ifaceSig ts).Op} {v : (ifaceSig ts).Ar e}
    {ev : PairWEv} (h : pairWDecAns ix e v = some ev) :
    ∃ r, (e.1.val = ix.word ∧ ∃ w, ev = .write (.atom w) [] r) ∨
      (e.1.val = ix.cons ∧ ∃ args, ev = .write .cons args r) := by
  unfold pairWDecAns at h
  rcases hr : retI32 v with _ | r
  · simp [hr] at h
  · simp only [hr, Option.bind_eq_bind, Option.bind_some] at h
    refine ⟨r, ?_⟩
    split_ifs at h with h1 h2
    · rcases hw : i64Arg e.2.1 with _ | w <;> simp [hw] at h
      exact .inl ⟨h1, w, h.symm⟩
    · rcases hp : i32Pair e.2.1 with _ | args <;> simp [hp] at h
      exact .inr ⟨h2, args, h.symm⟩

theorem pairWDecAsk_cases {ix : PairWImports} {e : (ifaceSig ts).Op} {ev : PairWEv}
    (h : pairWDecAsk ix e = some ev) :
    (∃ h, ev = .accept h) ∨ (ix.acceptAll = some e.1.val ∧ ev = .acceptAll) := by
  unfold pairWDecAsk at h
  split_ifs at h with h1 h2
  · rcases ha : i32Arg e.2.1 with _ | k <;> simp [ha] at h
    exact .inl ⟨k, h.symm⟩
  · cases h; exact .inr ⟨h2, rfl⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.Tree2
