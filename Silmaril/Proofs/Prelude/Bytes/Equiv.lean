module

public import Silmaril.Prelude.Bytes.Equiv.Defs
public import Silmaril.Prelude.Bytes.Write.Thms

/-! Proofs for `Silmaril.Prelude.Bytes.Equiv.Thms`. -/

@[expose] public section

namespace Silmaril.Proofs.Prelude.Bytes

open Silmaril Silmaril.KBytes

theorem equiv_iff {a b : KBytes} : a ≈ b ↔ a.toList = b.toList := Iff.rfl

theorem len_eq_of_equiv {a b : KBytes} (ha : a.wf = true) (hb : b.wf = true) (h : a ≈ b) :
    a.len = b.len := by
  rw [← length_toList a ha, ← length_toList b hb, equiv_iff.1 h]

theorem slice_congr {a b : KBytes} (ha : a.wf = true) (hb : b.wf = true) (h : a ≈ b)
    {off w : Nat} (hw : off + w ≤ a.len) : a.slice off w ≈ b.slice off w := by
  have hl := len_eq_of_equiv ha hb h
  show (a.slice off w).toList = (b.slice off w).toList
  rw [toList_slice a off w ha hw, toList_slice b off w hb (hl ▸ hw), equiv_iff.1 h]

theorem write_congr {a b : KBytes} (ha : a.wf = true) (hb : b.wf = true) (h : a ≈ b)
    {off w : Nat} (v : Nat) (hw : off + w ≤ a.len) : a.write off w v ≈ b.write off w v := by
  have hl := len_eq_of_equiv ha hb h
  show (a.write off w v).toList = (b.write off w v).toList
  rw [toList_write a off w v ha hw, toList_write b off w v hb (hl ▸ hw), equiv_iff.1 h]

theorem ropeWrite_congr {a b : KBytes} (ha : a.wf = true) (hb : b.wf = true) (h : a ≈ b)
    {off w : Nat} (v : Nat) (hw : off + w ≤ a.len) :
    a.ropeWrite off w v ≈ b.ropeWrite off w v := by
  have hl := len_eq_of_equiv ha hb h
  show (a.ropeWrite off w v).toList = (b.ropeWrite off w v).toList
  rw [toList_ropeWrite a off w v ha hw, toList_ropeWrite b off w v hb (hl ▸ hw), equiv_iff.1 h]

theorem toByteArray_eq_iff {a b : KBytes} : a.toByteArray = b.toByteArray ↔ a ≈ b := by
  constructor
  · intro h
    have := congrArg (fun x : ByteArray => x.data.toList) h
    exact equiv_iff.2 (by simpa [toByteArray] using this)
  · intro h
    simp only [toByteArray, equiv_iff.1 h]

end Silmaril.Proofs.Prelude.Bytes
