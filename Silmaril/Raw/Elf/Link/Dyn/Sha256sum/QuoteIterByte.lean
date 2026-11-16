module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.QuoteFrame

/-! # GNU `sha256sum`: the byte classes of `quotearg_buffer_restyled`'s loop

Facts about one byte `c` of a plain name (`isSafe c`), each checked by `decide` over the 256
byte values: the conditions the loop's blocks evaluate on it (`> 0x3f`, sign, `> 'z'`, `= '@'`,
the mask `0x3ffffff53ffffff` over `c - 0x41` at `0x5cd0` — `A-Z ] _ a-z`, and the
`quote_these_too` bit, set only for `:`, which `isSafe` excludes), and the address arithmetic of
the byte jump table (`0x7f74`) and of `quote_these_too`. -/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum

open Silmaril.X86 (Word Byte)
open Silmaril.X86.Ext

/-- A byte as the 64-bit value a one-byte load gives. -/
abbrev bw (c : Byte) : Word := BitVec.ofNat 64 c.toNat

/-- A byte of a plain name. -/
abbrev QSafe (c : Byte) : Prop := Silmaril.Apps.Sha256sum.isSafe (UInt8.ofBitVec c) = true

/-- The word of `quote_these_too` that holds the bit of `c` (`R-0x40 + 4 * (c / 32)`), for the
bytes of a plain name (`c ≥ 0x20`): only `:` (bit 26 of word 1) is set. -/
def qiQ (c : Byte) : Word := if c.toNat / 32 = 1 then 0x04000000#64 else 0#64

theorem qi_all {P : Byte → Prop} (h : ∀ n, n < 256 → P (BitVec.ofNat 8 n)) (c : Byte) : P c := by
  have := h c.toNat c.isLt
  simpa using this

theorem qi_lt (c : Byte) (h : QSafe c) : 0x25 ≤ c.toNat ∧ c.toNat ≤ 0x7a := by
  revert c h; apply qi_all; decide +kernel

theorem qi_rsi (c : Byte) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 8 (bw c)))) = bw c := by
  revert c; apply qi_all; decide +kernel

theorem qi_shl2 (c : Byte) : bw c <<< 2 = BitVec.ofNat 64 (4 * c.toNat) := by
  revert c; apply qi_all; decide +kernel

theorem qi_c50cd (c : Byte) (h : QSafe c) :
    Cond.eval (AluOp.flagsN Silmaril.X86.AluOp.cmp (BitVec.setWidth 8 (bw c)) (BitVec.setWidth 8 0#64))
      Cond.ne = some true := by
  revert c; apply qi_all; decide +kernel

theorem qi_c510b (c : Byte) (h : QSafe c) :
    Cond.eval (AluOp.flagsN Silmaril.X86.AluOp.cmp
        (BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 8 (bw c))))))
        (BitVec.setWidth 8 63#64)) Cond.g = some (decide (63 < c.toNat)) := by
  revert c; apply qi_all; decide +kernel

theorem qi_c5118 (c : Byte) (h : QSafe c) :
    Cond.eval (logicFlagsN (BitVec.setWidth 8 (bw c) &&& BitVec.setWidth 8 (bw c))) Cond.s = some false := by
  revert c; apply qi_all; decide +kernel

theorem qi_c5121 (c : Byte) (h : QSafe c) (hl : c.toNat ≤ 63) :
    Cond.eval (AluOp.flagsN Silmaril.X86.AluOp.cmp (BitVec.setWidth 8 (bw c)) (BitVec.setWidth 8 63#64))
      Cond.a = some false := by
  revert c; apply qi_all; decide +kernel

theorem qi_c5cc0 (c : Byte) (h : QSafe c) :
    Cond.eval (AluOp.flagsN Silmaril.X86.AluOp.cmp (BitVec.setWidth 8 (bw c)) (BitVec.setWidth 8 122#64))
      Cond.g = some false := by
  revert c; apply qi_all; decide +kernel

theorem qi_c5cc6 (c : Byte) (h : QSafe c) (hl : 63 < c.toNat) :
    Cond.eval (AluOp.flagsN Silmaril.X86.AluOp.cmp (BitVec.setWidth 8 (bw c)) (BitVec.setWidth 8 64#64))
      Cond.e = some false := by
  revert c; apply qi_all; decide +kernel

/-- **The letter mask at `0x5cd0`**: `1 << (c - 0x41)` meets `0x3ffffff53ffffff` for every
safe byte above `0x3f` (`A-Z ] _ a-z`). -/
theorem qi_c5cd0 (c : Byte) (h : QSafe c) (hl : 63 < c.toNat) :
    Cond.eval (logicFlagsN (BitVec.setWidth 64 (BitVec.setWidth 64 (ShiftOp.shl.result (BitVec.setWidth 64 1#64)
        ((BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (bw c + 18446744073709551551#64)))).toNat % 64)))
        &&& BitVec.setWidth 64 288230373266030591#64)) Cond.ne = some true := by
  revert c; apply qi_all; decide +kernel

/-- **The `quote_these_too` bit** of a safe byte is clear (`:` is not safe). -/
theorem qi_c5185 (c : Byte) (h : QSafe c) :
    Cond.eval (AluOp.flagsN Silmaril.X86.AluOp.and (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32
        (BitVec.setWidth 64 (ShiftOp.shr.result (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (qiQ c))))
          ((BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (bw c)))).toNat % 32))))))
        (BitVec.setWidth 32 1#64)) Cond.e = some true := by
  revert c; apply qi_all; unfold qiQ; decide +kernel

theorem qi_a5185 (c : Byte) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.ofNat 8 (c.toNat / 32)))) <<< 2 =
      BitVec.ofNat 64 (4 * (c.toNat / 32)) := by
  revert c; apply qi_all; decide +kernel

theorem qi_m8 (o n : Word) :
    ((o &&& ~~~(Silmaril.X86.Ext.narrowMask .b)) ||| (n.setWidth Silmaril.X86.Ext.Narrow.b.bits).setWidth 64).setWidth 8 =
      n.setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    Silmaril.X86.Ext.narrowMask, Silmaril.X86.Ext.Narrow.bits]
  have : i < 8 := hi
  obtain _|_|_|_|_|_|_|_|i := i
  all_goals first | omega | simp_all

end Silmaril.Elf.Link.Dyn.Sha256sum
