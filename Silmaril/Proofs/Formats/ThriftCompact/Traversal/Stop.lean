module

public import Silmaril.Formats.ThriftCompact.Traversal.Defs
import all Silmaril.Formats.ThriftCompact.Traversal.Defs

namespace Silmaril.Proofs.Formats.ThriftCompact.Traversal

open Silmaril.Formats Silmaril.Formats.ThriftCompact
open Silmaril.Formats.ThriftCompact.Traversal

private theorem header_stop {mode : VarintMode} {source : Bytes} {previous : Int}
    {offset next : Nat} (parsed : readFieldHeader mode previous source offset = .ok (.stop, next)) :
    next = offset + 1 ∧ source.data[offset]? = some 0 := by
  cases byteAt : source.data[offset]? with
  | none => simp [readFieldHeader, readOctet, byteAt, bind, Except.bind] at parsed
  | some byte =>
    by_cases zero : byte.toNat = 0
    · have byteZero : byte = 0 := UInt8.toNat_inj.mp zero
      subst byte
      simp [readFieldHeader, readOctet, byteAt, bind, Except.bind, pure, Except.pure] at parsed
      exact ⟨parsed.symm, rfl⟩
    · cases tag : ValueType.ofTag? (byte.toNat % 16) with
      | none => simp [readFieldHeader, readOctet, byteAt, zero, tag, bind, Except.bind] at parsed
      | some type =>
        simp only [readFieldHeader, readOctet, byteAt, zero, tag, bind, Except.bind,
          pure, Except.pure, ite_false] at parsed
        split at parsed
        · split at parsed
          · contradiction
          · split at parsed <;> simp at parsed
        · split at parsed <;> simp at parsed

private theorem fold_stop {α : Type} (reader : Reader) (read : Int → FieldType → α → Read α)
    (budget offset next : Nat) (previous : Int) (before after : α)
    (parsed : foldFields reader read budget previous before offset = .ok (after, next)) :
    ∃ stop, next = stop + 1 ∧ reader.source.data[stop]? = some 0 := by
  induction budget generalizing offset next previous before after with
  | zero =>
    rw [foldFields] at parsed
    cases line : readFieldHeader reader.mode previous reader.source offset with
    | error e => simp [compact, line, Except.mapError, bind, Except.bind] at parsed
    | ok result =>
      obtain ⟨header, atHeader⟩ := result
      cases header with
      | stop =>
        simp [compact, line, Except.mapError, bind, Except.bind, pure, Except.pure] at parsed
        exact ⟨offset, parsed.2.symm.trans (header_stop line).1, (header_stop line).2⟩
      | field id type => simp [compact, line, Except.mapError, bind, Except.bind] at parsed
  | succ budget ih =>
    rw [foldFields] at parsed
    cases line : readFieldHeader reader.mode previous reader.source offset with
    | error e => simp [compact, line, Except.mapError, bind, Except.bind] at parsed
    | ok result =>
      obtain ⟨header, atHeader⟩ := result
      cases header with
      | stop =>
        simp [compact, line, Except.mapError, bind, Except.bind, pure, Except.pure] at parsed
        exact ⟨offset, parsed.2.symm.trans (header_stop line).1, (header_stop line).2⟩
      | field id type =>
        cases step : read id type before atHeader with
        | error e => simp [compact, line, step, Except.mapError, bind, Except.bind] at parsed
        | ok result =>
          obtain ⟨updated, advanced⟩ := result
          have rest : foldFields reader read budget id updated advanced = .ok (after, next) := by
            simpa only [compact, line, step, Except.mapError, bind, Except.bind] using parsed
          exact ih advanced next id updated after rest

public theorem readStruct_stop {reader : Reader} {offset next : Nat} {fields : List Field}
    (parsed : readStruct reader offset = .ok (fields, next)) :
    ∃ stop, next = stop + 1 ∧ reader.source.data[stop]? = some 0 := by
  unfold readStruct at parsed
  split at parsed
  · rename_i depth depthEq
    simp only [bind, Except.bind, pure, Except.pure] at parsed
    split at parsed
    · contradiction
    · rename_i result fold
      obtain ⟨indexed, endOffset⟩ := result
      cases parsed
      exact fold_stop reader _ _ offset endOffset 0 [] indexed fold
  · contradiction

end Silmaril.Proofs.Formats.ThriftCompact.Traversal
