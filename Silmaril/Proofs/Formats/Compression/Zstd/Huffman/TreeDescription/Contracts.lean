module

public import Silmaril.Formats.Compression.Zstd.Huffman.TreeDescription.Defs
import Silmaril.Formats.Compression.Zstd.Huffman.DirectWeights.Thms
import Silmaril.Formats.Compression.Zstd.Huffman.FseWeights.Thms
import Silmaril.Formats.Compression.Zstd.Huffman.SingleStream.Thms
import Silmaril.Formats.Compression.Zstd.Huffman.Weights.Thms

public section

namespace Silmaril.Proofs.Formats.Compression.Zstd.Huffman.TreeDescription

open Silmaril.Formats.Compression.Zstd.Huffman
open Silmaril.Formats.Compression.Zstd.Huffman.TreeDescription

theorem read_sound {limits : Limits} {input : List UInt8} {result : Prefix}
    (success : TreeDescription.read limits input = .ok result) : result.Valid limits input := by
  cases input with
  | nil => cases success
  | cons header body =>
    simp only [TreeDescription.read] at success
    split at success
    · cases reading : DirectWeights.read limits.direct (header :: body) with
      | error reason => simp [reading, Except.mapError, Except.map] at success
      | ok parsed =>
        simp only [reading, Except.mapError, Except.map] at success
        cases success
        obtain ⟨wire, valid, cap⟩ := DirectWeights.read_sound reading
        exact ⟨.direct wire, valid, cap⟩
    · cases emitting : FseWeights.read limits.bytes (limits.tree.symbolCap - 1) (header :: body) with
      | error reason => simp [emitting, Except.mapError, bind, Except.bind] at success
      | ok parsed =>
        cases completed : Weights.complete limits.tree parsed.weights with
        | error reason => simp [emitting, completed, Except.mapError, bind, Except.bind] at success
        | ok tree =>
          simp only [emitting, completed, Except.mapError, bind, Except.bind, pure, Except.pure] at success
          cases success
          obtain ⟨wire, cap, _⟩ := FseWeights.read_sound emitting
          obtain ⟨completion, valid⟩ := Weights.complete_sound completed
          exact ⟨.fse wire completion, valid, cap⟩

theorem readTable_sound {limits : Limits} {input : List UInt8} {result : Prefix} {table : SingleStream.Table}
    (success : readTable limits input = .ok (result, table)) :
    TreeDescription.read limits input = .ok result ∧ result.Valid limits input ∧
      SingleStream.TableWire result.tree table := by
  cases reading : TreeDescription.read limits input with
  | error reason => simp [readTable, reading, bind, Except.bind] at success
  | ok parsed =>
    cases built : SingleStream.buildGeneral (limits.treeLimits parsed.mode) parsed.tree with
    | error reason => simp [readTable, reading, built, Except.mapError, bind, Except.bind] at success
    | ok canonical =>
      simp only [readTable, reading, built, Except.mapError, bind, Except.bind, pure, Except.pure] at success
      cases success
      exact ⟨rfl, read_sound reading, (SingleStream.buildGeneral_sound built).2⟩

theorem suffix_exact {input : List UInt8} {result : Prefix} (wire : Wire input result) :
    input.drop result.consumed = result.rest := by
  cases wire with
  | direct origin => exact DirectWeights.suffix_exact origin
  | fse origin _ => exact FseWeights.suffix_exact origin

private theorem dropLast_completion {written : List Nat} {tree : Weights.Tree}
    (completion : Weights.CompletionWire written tree) :
    Weights.CompletionWire tree.weights.dropLast tree := by
  obtain ⟨last, shape, bounds⟩ := completion
  have exactWritten : tree.weights.dropLast = written := by simp [shape]
  rw [exactWritten]
  exact ⟨last, shape, bounds⟩

theorem completion_wire {input : List UInt8} {result : Prefix} (wire : Wire input result) :
    Weights.CompletionWire result.transmitted result.tree := by
  cases wire with
  | direct origin =>
    obtain ⟨_, _, _, _, _, _, completion⟩ := origin
    exact dropLast_completion completion
  | fse _ completion => exact dropLast_completion completion

end Silmaril.Proofs.Formats.Compression.Zstd.Huffman.TreeDescription
