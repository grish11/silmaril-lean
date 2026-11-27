module

public import Silmaril.Machine.RegisterFile
public import Silmaril.Machine.AArch64.Flags.Defs

/-!
# AArch64 register state: `Width`, X0–X30, SP, PC, NZCV

The user-mode (EL0) register state of an A64 machine, and the two ways an instruction
can read and write a register number `n` in `0 … 31`:

* `readX` / `writeX` follow Arm's `X{}` accessor: register 31 is the **zero register**
  (it reads as zero and ignores writes).
* `readXSP` / `writeXSP` treat register 31 as the **stack pointer**, through `readSP` /
  `writeSP`, which follow Arm's `SP{}` accessor.

Which of the two an instruction uses is fixed by its pseudocode, operand by operand.
`setPC` and `setNZCV` update the program counter and the flags.

Sources (Arm A64 ISA XML 2026-09, Arm ARM DDI 0487 M.d):

* `X{}`: `shared_pseudocode.xml`, `aarch64/functions/registers/X`.
* `SP{}`: `shared_pseudocode.xml`, `aarch64/functions/registers/SP`.
* Register 31 is "either the current stack pointer or the zero register, depending on
  the instruction and the operand position": Arm ARM C1.2.6.1.
* 32-bit data size: "the upper 32 bits are ignored on a read and cleared to zero on a
  write": Arm ARM C1.2.6.1.

Assumptions: EL0 only, so `SP{}` always names `SP_EL0`. Only the 32-bit and 64-bit data
sizes are modelled; `X{}` can also read 8 or 16 bits, which no modelled instruction uses.

This is a handwritten model. It follows the Arm text; it makes no claim of equivalence
with the ASL or with any other model. `Silmaril.Machine.AArch64.State.Thms` proves the
register-31 and zero-extension rules.
-/

@[expose] public section

namespace Silmaril.Machine.AArch64

/-- The data size of an instruction: the `W` (32-bit) or `X` (64-bit) form. Instruction
pages compute it from the `sf` bit as `datasize = 32 << UInt(sf)`. -/
inductive Width where
  | w32
  | w64
deriving DecidableEq, Repr

/-- The number of bits of a data size. -/
abbrev Width.bits : Width → Nat
  | .w32 => 32
  | .w64 => 64

/-- A register number as it appears in a 5-bit encoding field (`Rd`, `Rn`, `Rm`, `Rt`).
The value 31 means the zero register or the stack pointer, depending on the accessor. -/
abbrev Reg := BitVec 5

/-- A register number other than 31 names one of R0–R30. -/
theorem Reg.toNat_lt_of_ne {n : Reg} (h : n ≠ 31#5) : n.toNat < 31 := by
  have : n.toNat ≠ 31 := fun h' => h (BitVec.eq_of_toNat_eq h')
  have := n.isLt
  omega

/-- The general-purpose register R0–R30 named by a register number other than 31. -/
def Reg.index (n : Reg) (h : n ≠ 31#5) : Fin 31 := ⟨n.toNat, Reg.toNat_lt_of_ne h⟩

/-- The EL0 register state.

There is no storage for register 31: the zero register has no state, and the stack
pointer is the separate field `sp`. So "writes to the zero register are ignored" holds by
construction. -/
structure State where
  /-- R0–R30, the 64-bit general-purpose registers (Arm's `_R`). -/
  regs : RegisterFile (Fin 31) (BitVec 64)
  /-- The stack pointer. At EL0 this is `SP_EL0`. -/
  sp : BitVec 64
  /-- The program counter. -/
  pc : BitVec 64
  /-- The condition flags PSTATE.{N, Z, C, V}. -/
  nzcv : NZCV

namespace State

/-- Read register `n` at data size `w`, with 31 as the zero register (Arm's `X{}` getter):

```
if n != 31 then
    return _R[[n]][rw-1:0];
else
    return Zeros{rw};
```
A 32-bit read takes the low 32 bits. -/
def readX (s : State) (w : Width) (n : Reg) : BitVec w.bits :=
  if h : n = 31#5 then 0#w.bits else (s.regs (n.index h)).setWidth w.bits

/-- Write `v` to register `n` at data size `w`, with 31 as the zero register (Arm's `X{}`
setter):

```
if n != 31 then
    _R[[n]] = ZeroExtend{64}(value);
end;
```
A 32-bit write clears bits 63:32. A write to register 31 leaves the state unchanged. -/
def writeX (s : State) (w : Width) (n : Reg) (v : BitVec w.bits) : State :=
  if h : n = 31#5 then s
  else { s with regs := RegisterFile.write s.regs (n.index h) (v.setWidth 64) }

/-- Read the stack pointer at data size `w` (Arm's `SP{}` getter at EL0:
`return SP_EL0()[width-1:0]`). -/
def readSP (s : State) (w : Width) : BitVec w.bits := s.sp.setWidth w.bits

/-- Write the stack pointer at data size `w` (Arm's `SP{}` setter at EL0:
`SP_EL0() = ZeroExtend{64}(value)`). A 32-bit write clears bits 63:32. -/
def writeSP (s : State) (w : Width) (v : BitVec w.bits) : State :=
  { s with sp := v.setWidth 64 }

/-- Read register `n` with 31 as the stack pointer.

Arm has no accessor of this name. Instruction pages that allow SP in an operand choose
between `SP{}` and `X{}` themselves, in the shape (paraphrased, not quoted)
`if n == 31 then SP{}() else X{}(n)`; for example ADD (immediate),
`add_addsub_imm.xml:188`, and LDRB (immediate), `ldrb_imm.xml:309-314`.

Loads and stores also call `CheckSPAlignment()` in the SP branch, before the read
(`ldrb_imm.xml:310`). `readXSP` does not: it is a plain register read, also used by
ADD (immediate), which does no alignment check. The check is the load or store
instruction's job in `step`, the instruction semantics, which are not part of this
module yet. -/
def readXSP (s : State) (w : Width) (n : Reg) : BitVec w.bits :=
  if n = 31#5 then s.readSP w else s.readX w n

/-- Write register `n` with 31 as the stack pointer.

As for `readXSP`, Arm has no accessor of this name; instruction pages write, in the shape
(paraphrased, not quoted) `if n == 31 then SP{}() = v else X{}(n) = v`; for example ADD
(immediate), `add_addsub_imm.xml:194-198`, and the LDRB writeback,
`ldrb_imm.xml:329-333`. ADD (immediate) writes `SP{64}() = ZeroExtend{64}(result)`; this
gives the same state as `writeSP w v`, because the `SP{}` setter zero-extends at both
widths. -/
def writeXSP (s : State) (w : Width) (n : Reg) (v : BitVec w.bits) : State :=
  if n = 31#5 then s.writeSP w v else s.writeX w n v

/-- Set the program counter. -/
def setPC (s : State) (pc : BitVec 64) : State := { s with pc := pc }

/-- Set the condition flags (Arm: `PSTATE.[N,Z,C,V] = nzcv`, as in ADDS and SUBS). -/
def setNZCV (s : State) (f : NZCV) : State := { s with nzcv := f }

end State

end Silmaril.Machine.AArch64
