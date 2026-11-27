module

public import Silmaril.Machine.AArch64.State.Defs
import Silmaril.Proofs.Machine.AArch64.State.Registers

/-!
# AArch64 register state: register 31 and zero-extension

* **Zero register.** `readX_zr`: register 31 reads as zero through `readX`. `writeX_zr`:
  a write to register 31 through `writeX` leaves the state unchanged. (Arm's `X{}`
  accessor; Arm ARM B1.2.3: "register number 31 accesses the zero register which reads as
  zero and ignores writes".)
* **W zero-extension.** `readX_writeX_w32` (for R0–R30, `n ≠ 31`): after a 32-bit write,
  the 64-bit register is the value zero-extended. `writeX_w32_high` (every `n`): bits 63:32
  are zero afterwards. `readX_w32`: a 32-bit read is the low 32 bits of the 64-bit
  register. The same holds for the stack pointer (`readSP_writeSP_w32`, `writeSP_w32_high`). (Arm ARM C1.2.6.1: "the upper 32 bits are
  ignored on a read and cleared to zero on a write".)
* **SP and ZR accessors differ only at 31.** `readXSP_of_ne`, `writeXSP_of_ne`: for
  `n ≠ 31` they are `readX`, `writeX`. `readXSP_31`, `writeXSP_31`: at 31 they are
  `readSP`, `writeSP`.
* **Read after write at any widths.** `readX_writeX_same` (for `n ≠ 31`), `readSP_writeSP`,
  `readXSP_writeXSP_same` (every `n`): the value written, zero-extended to 64 bits, then
  cut to the read width; `w` and `w'` may be unknown.
* Frame lemmas: what a write, `setPC` or `setNZCV` leaves unchanged, including the mixed
  cases `readX_writeXSP_other` and `readXSP_writeX_other`.

Simp normal form: `readX` / `writeX` whenever simp can show `n ≠ 31` (`readXSP_of_ne`,
`writeXSP_of_ne` are `@[simp]`), the 32-bit read `readX .w32 n` over
`(readX .w64 n).setWidth 32` (`readX_w64_setWidth_32`; its reverse `readX_w32` must not be
`@[simp]`), and, for the source width of a `setWidth`, the literal `32` over
`Width.w32.bits` (`Width.setWidth_w32_bits`).

Proofs longer than a few lines: module `Silmaril.Proofs.Machine.AArch64.State.Registers`.
-/

@[expose] public section

namespace Silmaril.Machine.AArch64

/-- For `rw`. Not `@[simp]`: simp already sees `Width.w32.bits` as `32`, so as a simp
lemma it never fires. -/
theorem Width.bits_w32 : Width.w32.bits = 32 := rfl

/-- For `rw`; not `@[simp]`, as for `Width.bits_w32`. -/
theorem Width.bits_w64 : Width.w64.bits = 64 := rfl

/-- Zero-extending to 64 bits and cutting back to the original width gives the value back
(every width is at most 64 bits). This is what a read at the width of the write reduces to. -/
@[simp] theorem Width.setWidth_setWidth_64 (w : Width) (v : BitVec w.bits) :
    (v.setWidth 64).setWidth w.bits = v := by
  cases w <;> exact (BitVec.setWidth_setWidth_of_le v (by decide)).trans (BitVec.setWidth_eq v)

/-- Re-index a value whose width is written `Width.w32.bits` to the literal `32`. A read
after a 32-bit write produces `@BitVec.setWidth Width.w32.bits 64 x`. Core's
`BitVec.setWidth_*` simp lemmas handle that form in some goals but not in two that a
`step` proof meets: a 32-bit write of a zero-extended byte read at 64 bits (simp is left
with `setWidth 64 (setWidth 32 b) = setWidth 64 b`) and a 32-bit write read back at 32
bits (left with `setWidth Width.w32.bits (setWidth 64 v) = v`). With this lemma both close.
On a literal `32` it rewrites a term to itself, so simp makes no progress and does not
loop. -/
@[simp] theorem Width.setWidth_w32_bits {k : Nat} (x : BitVec Width.w32.bits) :
    @BitVec.setWidth Width.w32.bits k x = @BitVec.setWidth 32 k x := rfl

namespace State

/-! ## Zero register -/

/-- Register 31 reads as zero through the `X{}` accessor. -/
@[simp] theorem readX_zr (s : State) (w : Width) : s.readX w 31#5 = 0#w.bits := by
  simp [readX]

/-- A write to register 31 through the `X{}` accessor changes nothing. -/
@[simp] theorem writeX_zr (s : State) (w : Width) (v : BitVec w.bits) :
    s.writeX w 31#5 v = s := by
  simp [writeX]

/-- For `n ≠ 31`, `readX` reads R`n` (the `n != 31` branch of the `X{}` getter). -/
theorem readX_of_ne (s : State) (w : Width) {n : Reg} (h : n ≠ 31#5) :
    s.readX w n = (s.regs (n.index h)).setWidth w.bits := by
  rw [readX, dite_eq_right h]

/-- For `n ≠ 31`, `writeX` writes R`n` zero-extended (the `n != 31` branch of the `X{}`
setter). -/
theorem writeX_of_ne (s : State) (w : Width) {n : Reg} (h : n ≠ 31#5) (v : BitVec w.bits) :
    s.writeX w n v = { s with regs := RegisterFile.write s.regs (n.index h) (v.setWidth 64) } := by
  rw [writeX, dite_eq_right h]

/-! ## Reads after writes -/

/-- **Read after write, any widths.** Write `v` at width `w` to R0–R30, read it back at
width `w'`: the value is `v` zero-extended to 64 bits (the `X{}` setter), then its low
`w'` bits (the `X{}` getter). Holds with `w` and `w'` unknown. -/
@[simp] theorem readX_writeX_same (s : State) {n : Reg} (h : n ≠ 31#5) (w w' : Width)
    (v : BitVec w.bits) :
    (s.writeX w n v).readX w' n = (v.setWidth 64).setWidth w'.bits := by
  simp [readX_of_ne _ _ h, writeX_of_ne _ _ h]

/-- **W zero-extension.** After a 32-bit write to R0–R30, the 64-bit register holds the
value zero-extended to 64 bits. The plain statement of the rule; simp derives it from
`readX_writeX_same`, so it is not `@[simp]`. -/
theorem readX_writeX_w32 (s : State) {n : Reg} (h : n ≠ 31#5) (v : BitVec 32) :
    (s.writeX .w32 n v).readX .w64 n = v.setWidth 64 := by
  simp [readX_of_ne _ _ h, writeX_of_ne _ _ h]

/-- A write to one register leaves every other register as it was, at any widths. -/
@[simp] theorem readX_writeX_other (s : State) {m n : Reg} (h : m ≠ n) (w w' : Width)
    (v : BitVec w.bits) : (s.writeX w n v).readX w' m = s.readX w' m :=
  Silmaril.Proofs.Machine.AArch64.State.readX_writeX_other s h w w' v

/-- The top 32 bits of a 32-bit value zero-extended to 64 bits are zero. -/
@[simp] theorem setWidth_64_high (v : BitVec 32) : (v.setWidth 64).extractLsb' 32 32 = 0#32 :=
  Silmaril.Proofs.Machine.AArch64.State.setWidth_64_high v

/-- **Bits 63:32 are zero after a 32-bit write**, for every register number (for 31 the
read is zero anyway). -/
theorem writeX_w32_high (s : State) (n : Reg) (v : BitVec 32) :
    ((s.writeX .w32 n v).readX .w64 n).extractLsb' 32 32 = 0#32 := by
  by_cases h : n = 31#5
  · subst h; simp
  · rw [readX_writeX_w32 s h, setWidth_64_high]

/-- A 32-bit read is the low 32 bits of the 64-bit register. -/
theorem readX_w32 (s : State) (n : Reg) : s.readX .w32 n = (s.readX .w64 n).setWidth 32 := by
  by_cases h : n = 31#5
  · subst h; simp
  · simp [readX_of_ne _ _ h]

/-- The low 32 bits of a 64-bit read are the 32-bit read: `readX_w32` read right to left,
which is the direction simp uses (the 32-bit read is the simpler form). Never make
`readX_w32` `@[simp]` as well: together they loop. -/
@[simp] theorem readX_w64_setWidth_32 (s : State) (n : Reg) :
    (s.readX .w64 n).setWidth 32 = s.readX .w32 n :=
  (readX_w32 s n).symm

/-- **Stack pointer read after write, any widths.** Write `v` at width `w`, read at width
`w'`: `v` zero-extended to 64 bits (the `SP{}` setter), then its low `w'` bits (the getter). -/
@[simp] theorem readSP_writeSP (s : State) (w w' : Width) (v : BitVec w.bits) :
    (s.writeSP w v).readSP w' = (v.setWidth 64).setWidth w'.bits := rfl

/-- **Stack pointer zero-extension.** After a 32-bit write, the 64-bit stack pointer holds
the value zero-extended to 64 bits. Simp derives it from `readSP_writeSP`, so it is not
`@[simp]`. -/
theorem readSP_writeSP_w32 (s : State) (v : BitVec 32) :
    (s.writeSP .w32 v).readSP .w64 = v.setWidth 64 := by
  simp [readSP, writeSP]

/-- Bits 63:32 of the stack pointer are zero after a 32-bit write. -/
theorem writeSP_w32_high (s : State) (v : BitVec 32) :
    ((s.writeSP .w32 v).readSP .w64).extractLsb' 32 32 = 0#32 := by
  rw [readSP_writeSP_w32, setWidth_64_high]

/-! ## The SP and ZR accessors differ only at register 31 -/

/-- For `n ≠ 31`, reading with 31-as-SP is reading with 31-as-ZR. Simp uses it whenever it can
show `n ≠ 31`, so for such registers the plain `X{}` accessor is the normal form. -/
@[simp] theorem readXSP_of_ne (s : State) (w : Width) {n : Reg} (h : n ≠ 31#5) :
    s.readXSP w n = s.readX w n := by
  rw [readXSP, ite_eq_right h]

/-- For `n ≠ 31`, writing with 31-as-SP is writing with 31-as-ZR. Simp uses it whenever it can
show `n ≠ 31`, so for such registers the plain `X{}` accessor is the normal form. -/
@[simp] theorem writeXSP_of_ne (s : State) (w : Width) {n : Reg} (h : n ≠ 31#5)
    (v : BitVec w.bits) : s.writeXSP w n v = s.writeX w n v := by
  rw [writeXSP, ite_eq_right h]

/-- At register 31, `readXSP` reads the stack pointer. -/
@[simp] theorem readXSP_31 (s : State) (w : Width) : s.readXSP w 31#5 = s.readSP w := by
  simp [readXSP]

/-- At register 31, `writeXSP` writes the stack pointer. -/
@[simp] theorem writeXSP_31 (s : State) (w : Width) (v : BitVec w.bits) :
    s.writeXSP w 31#5 v = s.writeSP w v := by
  simp [writeXSP]

/-- The two accessors really differ at 31: with SP = 16, `readX` gives 0 and `readXSP`
gives 16. -/
example :
    let s : State :=
      { regs := fun _ => 0, sp := 16, pc := 0, nzcv := ⟨false, false, false, false⟩ }
    s.readX .w64 31#5 = 0 ∧ s.readXSP .w64 31#5 = 16 := by
  decide

/-- **Read after write through the SP accessors, any widths.** No side condition: at 31
both name the stack pointer, otherwise both name R`n`. -/
@[simp] theorem readXSP_writeXSP_same (s : State) (w w' : Width) (n : Reg) (v : BitVec w.bits) :
    (s.writeXSP w n v).readXSP w' n = (v.setWidth 64).setWidth w'.bits := by
  by_cases h : n = 31#5
  · subst h; simp
  · simp [h]

/-- A write through `writeXSP` leaves every other register number's `readXSP` unchanged. -/
@[simp] theorem readXSP_writeXSP_other (s : State) {m n : Reg} (h : m ≠ n) (w w' : Width)
    (v : BitVec w.bits) : (s.writeXSP w n v).readXSP w' m = s.readXSP w' m :=
  Silmaril.Proofs.Machine.AArch64.State.readXSP_writeXSP_other s h w w' v

/-! ## Frame lemmas -/

@[simp] theorem writeX_sp (s : State) (w : Width) (n : Reg) (v : BitVec w.bits) :
    (s.writeX w n v).sp = s.sp := by
  unfold writeX; split <;> rfl

@[simp] theorem writeX_pc (s : State) (w : Width) (n : Reg) (v : BitVec w.bits) :
    (s.writeX w n v).pc = s.pc := by
  unfold writeX; split <;> rfl

@[simp] theorem writeX_nzcv (s : State) (w : Width) (n : Reg) (v : BitVec w.bits) :
    (s.writeX w n v).nzcv = s.nzcv := by
  unfold writeX; split <;> rfl

@[simp] theorem writeSP_regs (s : State) (w : Width) (v : BitVec w.bits) :
    (s.writeSP w v).regs = s.regs := rfl

@[simp] theorem writeSP_pc (s : State) (w : Width) (v : BitVec w.bits) :
    (s.writeSP w v).pc = s.pc := rfl

@[simp] theorem writeSP_nzcv (s : State) (w : Width) (v : BitVec w.bits) :
    (s.writeSP w v).nzcv = s.nzcv := rfl

/-- Writing the stack pointer leaves every `X{}` read unchanged. -/
@[simp] theorem readX_writeSP (s : State) (w w' : Width) (v : BitVec w.bits) (n : Reg) :
    (s.writeSP w v).readX w' n = s.readX w' n := rfl

/-- Writing a register through `X{}` leaves the stack pointer unchanged. -/
@[simp] theorem readSP_writeX (s : State) (w w' : Width) (n : Reg) (v : BitVec w.bits) :
    (s.writeX w n v).readSP w' = s.readSP w' := by
  simp [readSP]

@[simp] theorem writeSP_sp (s : State) (w : Width) (v : BitVec w.bits) :
    (s.writeSP w v).sp = v.setWidth 64 := rfl

/-- The register file after `writeX`, for any register number. Not `@[simp]`, so that goals
with an unknown `n` are not filled with `dite`; use `writeX_regs_of_ne` or `writeX_zr`. -/
theorem writeX_regs (s : State) (w : Width) (n : Reg) (v : BitVec w.bits) :
    (s.writeX w n v).regs =
      if h : n = 31#5 then s.regs else RegisterFile.write s.regs (n.index h) (v.setWidth 64) := by
  unfold writeX; split <;> rfl

/-- The register file after `writeX` to R0–R30: R`n` holds `v` zero-extended. -/
@[simp] theorem writeX_regs_of_ne (s : State) (w : Width) {n : Reg} (h : n ≠ 31#5)
    (v : BitVec w.bits) :
    (s.writeX w n v).regs = RegisterFile.write s.regs (n.index h) (v.setWidth 64) := by
  rw [writeX_of_ne _ _ h]

/-! ### `writeXSP` -/

@[simp] theorem writeXSP_pc (s : State) (w : Width) (n : Reg) (v : BitVec w.bits) :
    (s.writeXSP w n v).pc = s.pc := by
  unfold writeXSP; split <;> simp

@[simp] theorem writeXSP_nzcv (s : State) (w : Width) (n : Reg) (v : BitVec w.bits) :
    (s.writeXSP w n v).nzcv = s.nzcv := by
  unfold writeXSP; split <;> simp

/-- For `n ≠ 31`, `writeXSP` leaves the stack pointer unchanged. Not `@[simp]`: simp
already gets it from `writeXSP_of_ne` and `writeX_sp`. -/
theorem writeXSP_sp_of_ne (s : State) (w : Width) {n : Reg} (h : n ≠ 31#5)
    (v : BitVec w.bits) : (s.writeXSP w n v).sp = s.sp := by
  rw [writeXSP_of_ne _ _ h, writeX_sp]

/-- At 31, `writeXSP` leaves R0–R30 unchanged. -/
theorem writeXSP_regs_31 (s : State) (w : Width) (v : BitVec w.bits) :
    (s.writeXSP w 31#5 v).regs = s.regs := by
  simp

/-! ### Mixed accessors: `readX` after `writeXSP`, `readXSP` after `writeX` -/

/-- A write through `writeXSP` to `n` leaves `readX` of every other number unchanged
(for `n = 31` the write goes to SP, which `readX` never reads). -/
@[simp] theorem readX_writeXSP_other (s : State) {m n : Reg} (h : m ≠ n) (w w' : Width)
    (v : BitVec w.bits) : (s.writeXSP w n v).readX w' m = s.readX w' m := by
  by_cases hn : n = 31#5
  · subst hn; simp
  · rw [writeXSP_of_ne _ _ hn, readX_writeX_other _ h]

/-- A write through `writeX` to `n` leaves `readXSP` of every other number unchanged
(for `m = 31` the read is SP, which `writeX` never writes). -/
@[simp] theorem readXSP_writeX_other (s : State) {m n : Reg} (h : m ≠ n) (w w' : Width)
    (v : BitVec w.bits) : (s.writeX w n v).readXSP w' m = s.readXSP w' m := by
  by_cases hm : m = 31#5
  · subst hm; simp
  · rw [readXSP_of_ne _ _ hm, readXSP_of_ne _ _ hm, readX_writeX_other _ h]

/-! ### `setPC` and `setNZCV` -/

@[simp] theorem setPC_pc (s : State) (p : BitVec 64) : (s.setPC p).pc = p := rfl
@[simp] theorem setPC_regs (s : State) (p : BitVec 64) : (s.setPC p).regs = s.regs := rfl
@[simp] theorem setPC_sp (s : State) (p : BitVec 64) : (s.setPC p).sp = s.sp := rfl
@[simp] theorem setPC_nzcv (s : State) (p : BitVec 64) : (s.setPC p).nzcv = s.nzcv := rfl

@[simp] theorem readX_setPC (s : State) (p : BitVec 64) (w : Width) (n : Reg) :
    (s.setPC p).readX w n = s.readX w n := rfl
@[simp] theorem readSP_setPC (s : State) (p : BitVec 64) (w : Width) :
    (s.setPC p).readSP w = s.readSP w := rfl
@[simp] theorem readXSP_setPC (s : State) (p : BitVec 64) (w : Width) (n : Reg) :
    (s.setPC p).readXSP w n = s.readXSP w n := rfl

@[simp] theorem setNZCV_nzcv (s : State) (f : NZCV) : (s.setNZCV f).nzcv = f := rfl
@[simp] theorem setNZCV_regs (s : State) (f : NZCV) : (s.setNZCV f).regs = s.regs := rfl
@[simp] theorem setNZCV_sp (s : State) (f : NZCV) : (s.setNZCV f).sp = s.sp := rfl
@[simp] theorem setNZCV_pc (s : State) (f : NZCV) : (s.setNZCV f).pc = s.pc := rfl

@[simp] theorem readX_setNZCV (s : State) (f : NZCV) (w : Width) (n : Reg) :
    (s.setNZCV f).readX w n = s.readX w n := rfl
@[simp] theorem readSP_setNZCV (s : State) (f : NZCV) (w : Width) :
    (s.setNZCV f).readSP w = s.readSP w := rfl
@[simp] theorem readXSP_setNZCV (s : State) (f : NZCV) (w : Width) (n : Reg) :
    (s.setNZCV f).readXSP w n = s.readXSP w n := rfl

end State

end Silmaril.Machine.AArch64
