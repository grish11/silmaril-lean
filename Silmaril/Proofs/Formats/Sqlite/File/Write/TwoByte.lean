module
public import Silmaril.Formats.Sqlite.File.Write.Defs

public section
namespace Silmaril.Proofs.Formats.Sqlite.File.Write

open Silmaril.Formats Silmaril.Formats.Sqlite

private theorem read_two (view : File.View) (offset : Nat) :
    view.be? offset 2 = (do
      let high ← view.get? offset
      let low ← view.get? (offset + 1)
      pure (high.toNat * 256 + low.toNat)) := by
  let step (acc i : Nat) : Option Nat := do
    pure (acc * 256 + (← view.get? (offset + i)).toNat)
  change [0, 1].foldlM step 0 = _
  cases high : view.get? offset <;> simp [List.foldlM, step, high]

theorem be?_be_two (view : File.View) (offset value : Nat)
    (fits : value < 256 ^ 2)
    (bytes : ∀ i, i < 2 → view.get? (offset + i) = (File.Write.be 2 value)[i]?) :
    view.be? offset 2 = some value := by
  have high : view.get? (offset + 0) = some (UInt8.ofNat (value / 256)) :=
    bytes 0 (by decide)
  rw [Nat.add_zero] at high
  have low : view.get? (offset + 1) = some (UInt8.ofNat (value / 1)) :=
    bytes 1 (by decide)
  rw [Nat.div_one] at low
  rw [read_two, high, low]
  simp [UInt8.toNat_ofNat']
  have bound : value / 256 < 256 := (Nat.div_lt_iff_lt_mul (by decide)).mpr fits
  rw [Nat.mod_eq_of_lt bound, Nat.mul_comm _ 256, Nat.div_add_mod]

theorem be?_two_truncated (view : File.View) (offset : Nat)
    (truncated : view.length < offset + 2) :
    view.be? offset 2 = none := by
  have missing : view.get? (offset + 1) = none := by
    unfold File.View.get?
    exact ite_eq_right (by omega)
  rw [read_two, missing]
  cases view.get? offset <;> rfl

theorem header_pageSize :
    (File.View.ofBytes (Bytes.ofList File.Write.header)).be? 16 2 = some File.Write.pageSize := by
  apply be?_be_two _ _ _ (by decide)
  intro i valid
  have cases : i = 0 ∨ i = 1 := by omega
  rcases cases with rfl | rfl <;> rfl

end Silmaril.Proofs.Formats.Sqlite.File.Write
