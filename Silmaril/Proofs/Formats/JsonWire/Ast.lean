module

public import Silmaril.Formats.JsonWire.Ast.Defs

@[expose] public section

namespace Silmaril.Proofs.Formats.JsonWire.Ast

open Silmaril.Formats.JsonWire

private theorem unitsChars_append (char : Char) (rest : Units) :
    unitsChars? (charUnits char ++ rest) = (unitsChars? rest).map (char :: ·) := by
  have valid : Char.isValidCharNat char.toNat := char.valid
  unfold charUnits
  split
  · rename_i bmp
    have unit : (UInt16.ofNat char.toNat).toNat = char.toNat := by
      exact UInt16.toNat_ofNat_of_lt' bmp
    have high : ¬(0xD800 ≤ char.toNat ∧ char.toNat ≤ 0xDBFF) := by omega
    have low : ¬(0xDC00 ≤ char.toNat ∧ char.toNat ≤ 0xDFFF) := by omega
    cases rest <;> simp only [List.singleton_append, unitsChars?, unit, Bool.and_eq_true,
      decide_eq_true_eq, high, low, ite_false, Char.ofNat_toNat, Option.map_eq_bind] <;> rfl
  · rename_i supplementary
    let offset := char.toNat - 0x10000
    have offsetBound : offset < 0x100000 := by dsimp [offset]; omega
    have high := show (UInt16.ofNat (0xD800 + offset / 0x400)).toNat = 0xD800 + offset / 0x400 by
      exact UInt16.toNat_ofNat_of_lt' (by change _ < 65536; omega)
    have low := show (UInt16.ofNat (0xDC00 + offset % 0x400)).toNat = 0xDC00 + offset % 0x400 by
      exact UInt16.toNat_ofNat_of_lt' (by change _ < 65536; omega)
    have recover : 0x10000 + (0xD800 + offset / 0x400 - 0xD800) * 0x400 +
        (0xDC00 + offset % 0x400) - 0xDC00 = char.toNat := by dsimp [offset]; omega
    change unitsChars? (UInt16.ofNat (0xD800 + offset / 0x400) ::
      UInt16.ofNat (0xDC00 + offset % 0x400) :: rest) = _
    have highRange : 0xD800 ≤ 0xD800 + offset / 0x400 ∧ 0xD800 + offset / 0x400 ≤ 0xDBFF := by omega
    have lowRange : 0xDC00 ≤ 0xDC00 + offset % 0x400 ∧ 0xDC00 + offset % 0x400 ≤ 0xDFFF := by omega
    simp only [unitsChars?, high, low, Bool.and_eq_true, decide_eq_true_eq, highRange, lowRange,
      and_self, ite_true, recover, Char.ofNat_toNat, Option.map_eq_bind]
    rfl

private theorem unitsChars_flatMap (chars : List Char) :
    unitsChars? (chars.flatMap charUnits) = some chars := by
  induction chars with
  | nil => rfl
  | cons _ _ ih => simp [unitsChars_append, ih]

theorem unitsString_stringUnits (text : String) : unitsString? (stringUnits text) = some text := by
  simp [unitsString?, stringUnits, unitsChars_flatMap]

end Silmaril.Proofs.Formats.JsonWire.Ast
