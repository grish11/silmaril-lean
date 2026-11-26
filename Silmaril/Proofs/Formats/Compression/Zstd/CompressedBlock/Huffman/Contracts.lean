module

public import Silmaril.Formats.Compression.Zstd.CompressedBlock.Huffman.Defs
import Silmaril.Formats.Compression.Zstd.CompressedBlock.Thms
import Silmaril.Formats.Compression.Zstd.Huffman.LiteralState.Thms

public section

namespace Silmaril.Proofs.Formats.Compression.Zstd.CompressedBlock.Huffman

open Silmaril.Formats.Compression.Zstd
open Silmaril.Formats.Compression.Zstd.Huffman
open Silmaril.Formats.Compression.Zstd.CompressedBlock (Limits)
open Silmaril.Formats.Compression.Zstd.CompressedBlock.Huffman

theorem decode_sound {profile : TreeDescription.Limits} {limits : Limits} {prior : State profile}
    {declaredSize : Nat} {body : List UInt8} {result : Result profile} (accepted : prior.block.tables.Valid)
    (success : CompressedBlock.Huffman.decode limits prior declaredSize body = .ok result) :
    body.length = declaredSize ∧ declaredSize ≤ limits.inputCapacity ∧
      result.bytes.length ≤ limits.execution.capacity ∧ result.next.block.Valid limits.window ∧
      BlockWire limits prior body result := by
  unfold CompressedBlock.Huffman.decode at success
  cases extent : CompressedBlock.Internal.checkExtent limits declaredSize body with
  | error reason => simp [extent, Except.mapError, bind, Except.bind] at success
  | ok successUnit =>
    cases successUnit
    obtain ⟨size, inputBound⟩ := CompressedBlock.Internal.checkExtent_iff.mp extent
    cases read : LiteralState.read (literalLimits limits profile) prior.literals body with
    | error reason => simp [extent, read, Except.mapError, bind, Except.bind] at success
    | ok parsed =>
      cases execute : CompressedBlock.Internal.execute limits prior.block parsed.literals parsed.rest with
      | error reason => simp [extent, read, execute, Except.mapError, bind, Except.bind] at success
      | ok out =>
        simp only [extent, read, execute, Except.mapError, bind, Except.bind, pure, Except.pure] at success
        cases success
        obtain ⟨wire, literalInput, literalCount, literalOutput⟩ := LiteralState.read_sound read
        simp only [literalLimits, LiteralSection.Limits.inputCap, LiteralSection.Limits.outputCap]
          at literalInput literalOutput
        obtain ⟨literalBytes, splitBody, prefixCount⟩ := LiteralState.consumption_exact wire
        obtain ⟨outputBound, nextValid, seqWire⟩ := CompressedBlock.Internal.execute_sound accepted execute
        exact ⟨size, inputBound, outputBound, nextValid, parsed, literalBytes, wire, splitBody, prefixCount,
          (Nat.le_trans literalInput (Nat.min_le_left _ _)), literalCount,
          (Nat.le_trans literalOutput (Nat.min_le_left _ _)), rfl, seqWire⟩

theorem decode_suffix_failure {profile : TreeDescription.Limits} {limits : Limits} {prior : State profile}
    {declaredSize : Nat} {body : List UInt8} {parsed : LiteralState.Result profile}
    {reason : CompressedBlock.Error}
    (fits : declaredSize ≤ limits.inputCapacity) (extent : body.length = declaredSize)
    (read : LiteralState.read (literalLimits limits profile) prior.literals body = .ok parsed)
    (failed : CompressedBlock.Internal.execute limits prior.block parsed.literals parsed.rest = .error reason) :
    CompressedBlock.Huffman.decode limits prior declaredSize body = .error (.block reason) := by
  have checked := CompressedBlock.Internal.checkExtent_iff.mpr ⟨extent, fits⟩
  simp [CompressedBlock.Huffman.decode, checked, read, failed, Except.mapError, bind, Except.bind]

end Silmaril.Proofs.Formats.Compression.Zstd.CompressedBlock.Huffman
