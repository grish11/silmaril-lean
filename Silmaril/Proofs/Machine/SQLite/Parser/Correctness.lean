module

public import Silmaril.Machine.SQLite.Parser.Defs
import Silmaril.Machine.SQLite.Tokenizer.Thms

public section

namespace Silmaril.Proofs.Machine.SQLite.Parser

open Silmaril.Machine.SQLite.Parser
open Silmaril.Machine.SQLite

theorem parse_sound {tokens : State} {stmt : Statement} (h : parse tokens = some stmt) :
    Grammar tokens stmt := by
  rw [parse.eq_def] at h
  split at h
  · dsimp only at h
    split at h
    · rename_i checked
      obtain ⟨rfl, rfl, rfl, rfl, wellFormed, terminator⟩ := checked
      cases h
      rcases terminator with rfl | rfl
      · exact ⟨wellFormed, Or.inl rfl⟩
      · exact ⟨wellFormed, Or.inr rfl⟩
    · contradiction
  · contradiction

theorem parse_complete {tokens : State} {stmt : Statement} (h : Grammar tokens stmt) :
    parse tokens = some stmt := by
  rcases h with ⟨wellFormed, rfl | rfl⟩ <;> simp [printTokens, parse, wellFormed]

theorem represents_print {stmt : Statement} (h : stmt.WellFormed) :
    Represents (print stmt) stmt := by
  refine ⟨printTokens stmt, ?_, h, Or.inl rfl⟩
  rw [print, String.toList_ofList]
  apply Tokenizer.lexes_render
  intro token mem
  simp only [printTokens, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide
  · exact h.2.1
  · decide
  · exact h.1.1
  · decide
  · decide
  · trivial
  · trivial

end Silmaril.Proofs.Machine.SQLite.Parser
