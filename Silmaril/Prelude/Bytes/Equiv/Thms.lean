module

public import Silmaril.Prelude.Bytes.Equiv.Defs
public import Silmaril.Prelude.Bytes.Write.Thms
import Silmaril.Proofs.Prelude.Bytes.Equiv

/-! # Kernel bytes up to their bytes: laws and congruences

Proofs of more than a few lines are in `Silmaril.Proofs.Prelude.Bytes.Equiv`. Each congruence
states the hypotheses it needs: none for operations defined through `toList`, `wf` of both sides
(and the window in range) for operations that use cached lengths.
-/

@[expose] public section

namespace Silmaril.KBytes

/-! ## The relation -/

theorem equiv_iff {a b : KBytes} : a ≈ b ↔ a.toList = b.toList := Iff.rfl

@[refl] theorem equiv_refl (a : KBytes) : a ≈ a := Setoid.refl a

theorem equiv_symm {a b : KBytes} (h : a ≈ b) : b ≈ a := Setoid.symm h

theorem equiv_trans {a b c : KBytes} (h₁ : a ≈ b) (h₂ : b ≈ c) : a ≈ c := Setoid.trans h₁ h₂

instance : Trans (α := KBytes) (· ≈ ·) (· ≈ ·) (· ≈ ·) := ⟨equiv_trans⟩

theorem equiv_of_eq {a b : KBytes} (h : a = b) : a ≈ b := h ▸ equiv_refl a

/-- Same bytes, as `ByteArray`s. -/
theorem toByteArray_eq_iff {a b : KBytes} : a.toByteArray = b.toByteArray ↔ a ≈ b :=
  Proofs.Prelude.Bytes.toByteArray_eq_iff

/-! ## Deciding it

The checks of `Silmaril.Prelude.Bytes` are sound for `≈` on any shapes. On canonical trees `beq`
is also complete, and the kernel compares canonical trees cheaply; there is deliberately no
`Decidable` instance, which would compare byte lists one cell per byte. -/

theorem equiv_of_beq {a b : KBytes} (h : a.beq b = true) : a ≈ b := toList_eq_of_beq a b h

theorem equiv_of_sameBytes (w : Nat) {a b : KBytes} (ha : a.wf = true) (hb : b.wf = true)
    (h : a.sameBytes w b = true) : a ≈ b :=
  toList_eq_of_sameBytes w a b ha hb h

theorem equiv_of_canon_beq (c : Nat) {a b : KBytes} (ha : a.wf = true) (hb : b.wf = true)
    (h : (a.canon c).beq (b.canon c) = true) : a ≈ b := by
  have := toList_eq_of_beq _ _ h; rwa [toList_canon c a ha, toList_canon c b hb] at this

/-! ## Congruences for every tree -/

theorem append_congr {a a' b b' : KBytes} (ha : a ≈ a') (hb : b ≈ b') : a ++ b ≈ a' ++ b' := by
  show (a ++ b).toList = (a' ++ b').toList; rw [toList_append, toList_append, ha, hb]

/-- `canon` keeps the bytes (`wf` needed: canon reads through cached lengths). -/
theorem canon_equiv (c : Nat) {a : KBytes} (ha : a.wf = true) : a.canon c ≈ a :=
  toList_canon c a ha

/-! ## Congruences for trees with correct cached lengths -/

theorem len_eq_of_equiv {a b : KBytes} (ha : a.wf = true) (hb : b.wf = true) (h : a ≈ b) :
    a.len = b.len :=
  Proofs.Prelude.Bytes.len_eq_of_equiv ha hb h

theorem readLE_congr {a b : KBytes} (ha : a.wf = true) (hb : b.wf = true) (h : a ≈ b)
    (off w : Nat) : a.readLE off w = b.readLE off w := by
  rw [readLE_eq a ha, readLE_eq b hb, equiv_iff.1 h]

theorem get?_congr {a b : KBytes} (ha : a.wf = true) (hb : b.wf = true) (h : a ≈ b) (i : Nat) :
    a.get? i = b.get? i := by
  rw [get?_eq a ha, get?_eq b hb, equiv_iff.1 h]

theorem read_congr {a b : KBytes} (ha : a.wf = true) (hb : b.wf = true) (h : a ≈ b)
    {off w : Nat} (hw : off + w ≤ a.len) : a.read off w = b.read off w := by
  rw [read_eq a off w ha hw, read_eq b off w hb (len_eq_of_equiv ha hb h ▸ hw), equiv_iff.1 h]

theorem slice_congr {a b : KBytes} (ha : a.wf = true) (hb : b.wf = true) (h : a ≈ b)
    {off w : Nat} (hw : off + w ≤ a.len) : a.slice off w ≈ b.slice off w :=
  Proofs.Prelude.Bytes.slice_congr ha hb h hw

theorem canon_congr (c : Nat) {a b : KBytes} (ha : a.wf = true) (hb : b.wf = true) (h : a ≈ b) :
    a.canon c ≈ b.canon c :=
  equiv_trans (canon_equiv c ha) (equiv_trans h (equiv_symm (canon_equiv c hb)))

theorem write_congr {a b : KBytes} (ha : a.wf = true) (hb : b.wf = true) (h : a ≈ b)
    {off w : Nat} (v : Nat) (hw : off + w ≤ a.len) : a.write off w v ≈ b.write off w v :=
  Proofs.Prelude.Bytes.write_congr ha hb h v hw

theorem ropeWrite_congr {a b : KBytes} (ha : a.wf = true) (hb : b.wf = true) (h : a ≈ b)
    {off w : Nat} (v : Nat) (hw : off + w ≤ a.len) :
    a.ropeWrite off w v ≈ b.ropeWrite off w v :=
  Proofs.Prelude.Bytes.ropeWrite_congr ha hb h v hw

/-- The two writes give equivalent trees (different shapes, same bytes). -/
theorem ropeWrite_equiv_write {t : KBytes} (ht : t.wf = true) {off w : Nat} (v : Nat)
    (hw : off + w ≤ t.len) : t.ropeWrite off w v ≈ t.write off w v := by
  show _ = _; rw [toList_ropeWrite t off w v ht hw, toList_write t off w v ht hw]

/-! ## Equivalence is not structural equality -/

/-- One leaf and a node of two leaves hold the same two bytes. -/
example : leaf 2 0x0201 ≈ node 2 (leaf 1 1) (leaf 1 2) ∧ leaf 2 0x0201 ≠ node 2 (leaf 1 1) (leaf 1 2) :=
  ⟨rfl, fun h => KBytes.noConfusion h⟩

/-- A leaf's digits beyond its length are not bytes. -/
example : leaf 1 0x0101 ≈ leaf 1 1 := rfl

/-- On a malformed tree (cached length 5 for two bytes), `≈` still holds by the bytes, and `len`
is not respected: the `wf` hypotheses of the congruences above are needed. -/
example : node 5 (leaf 1 1) (leaf 1 2) ≈ leaf 2 0x0201 ∧
    (node 5 (leaf 1 1) (leaf 1 2)).len ≠ (leaf 2 0x0201).len :=
  ⟨rfl, by decide⟩

end Silmaril.KBytes
