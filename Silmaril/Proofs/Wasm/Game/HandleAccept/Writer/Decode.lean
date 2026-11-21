module

public import Silmaril.Wasm.Game.HandleAccept.Writer.Defs

/-! # Proofs: what the writer decoders produce -/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Writers

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game
  Silmaril.Wasm.Game.HandleAccept Silmaril.Wasm.Game.HandleAccept.Writers
  Silmaril.Accept.Handle Silmaril.Formats.Api

theorem i32Args_length : ∀ {vs : List Val} {hs : List (BitVec 32)}, i32Args vs = some hs →
    hs.length = vs.length
  | [], hs, h => by simp [i32Args] at h; subst h; rfl
  | .num ⟨.int .i32, a⟩ :: vs, hs, h => by
      simp only [i32Args, Option.map_eq_some_iff] at h
      obtain ⟨hs', h', rfl⟩ := h
      exact congrArg (· + 1) (i32Args_length h')
  | .num ⟨.int .i64, _⟩ :: _, _, h => by simp [i32Args] at h
  | .num ⟨.float _, _⟩ :: _, _, h => by simp [i32Args] at h
  | .vec _ :: _, _, h => by simp [i32Args] at h
  | .ref _ :: _, _, h => by simp [i32Args] at h

theorem i32Pair_length {vs : List Val} {hs : List (BitVec 32)} (h : i32Pair vs = some hs) :
    hs.length = 2 := by
  unfold i32Pair at h
  split at h <;> cases h; rfl

variable {ts : List FnType}

theorem typed_length (e : (ifaceSig ts).Op) : e.2.1.length = (ts.get e.1).params.length :=
  e.2.2.length_eq.symm

/-! ## The cons writer API -/

theorem consWDecAns_cases {ix : ConsWImports} {e : (ifaceSig ts).Op} {v : (ifaceSig ts).Ar e}
    {ev : ConsWEv} (h : consWDecAns ix e v = some ev) :
    ∃ r, (e.1.val = ix.word ∧ ∃ w, ev = .write (.atom w) [] r) ∨
      (e.1.val = ix.nil ∧ ev = .write .nil [] r) ∨
      (e.1.val = ix.cons ∧ ∃ args, args.length = 2 ∧ ev = .write .cons args r) := by
  unfold consWDecAns at h
  rcases hr : retI32 v with _ | r
  · simp [hr] at h
  · simp only [hr, Option.bind_eq_bind, Option.bind_some] at h
    refine ⟨r, ?_⟩
    split_ifs at h with h1 h2 h3 h4
    · rcases hw : i64Arg e.2.1 with _ | w <;> simp [hw] at h
      exact .inl ⟨h1, w, h.symm⟩
    · simp at h
      exact .inr (.inl ⟨h2, h.symm⟩)
    · rcases hp : i32Pair e.2.1 with _ | args <;> simp [hp] at h
      exact .inr (.inr ⟨h4, args, i32Pair_length hp, h.symm⟩)

theorem consWDecAsk_cases {ix : ConsWImports} {e : (ifaceSig ts).Op} {ev : ConsWEv}
    (h : consWDecAsk ix e = some ev) :
    (∃ h, ev = .accept h) ∨ (ix.acceptAll = some e.1.val ∧ ev = .acceptAll) := by
  unfold consWDecAsk at h
  split_ifs at h with h1 h2
  · rcases ha : i32Arg e.2.1 with _ | k <;> simp [ha] at h
    exact .inl ⟨k, h.symm⟩
  · cases h; exact .inr ⟨h2, rfl⟩

/-! ## The n-ary writer API -/

theorem sxWDecAns_cases {ix : SxWImports} {e : (ifaceSig ts).Op} {v : (ifaceSig ts).Ar e}
    {ev : SxWEv} (h : sxWDecAns ix e v = some ev) :
    ∃ r, (e.1.val = ix.word ∧ ∃ w, ev = .write (.atom w) [] r) ∨
      (e.1.val ∈ ix.lists ∧ ∃ args, args.length = (ts.get e.1).params.length ∧
        ev = .write .list args r) := by
  unfold sxWDecAns at h
  rcases hr : retI32 v with _ | r
  · simp [hr] at h
  · simp only [hr, Option.bind_eq_bind, Option.bind_some] at h
    refine ⟨r, ?_⟩
    split_ifs at h with h1 h2
    · rcases hw : i64Arg e.2.1 with _ | w <;> simp [hw] at h
      exact .inl ⟨h1, w, h.symm⟩
    · rcases hp : i32Args e.2.1 with _ | args <;> simp [hp] at h
      exact .inr ⟨h2, args, (i32Args_length hp).trans (typed_length e), h.symm⟩

theorem sxWDecAsk_cases {ix : SxWImports} {e : (ifaceSig ts).Op} {ev : SxWEv}
    (h : sxWDecAsk ix e = some ev) :
    (∃ h, ev = .accept h) ∨ (ix.acceptAll = some e.1.val ∧ ev = .acceptAll) := by
  unfold sxWDecAsk at h
  split_ifs at h with h1 h2
  · rcases ha : i32Arg e.2.1 with _ | k <;> simp [ha] at h
    exact .inl ⟨k, h.symm⟩
  · cases h; exact .inr ⟨h2, rfl⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.Writers
