module

public import Silmaril.Wasm.Wat
public import Silmaril.Sim.RV64.Ref.Defs
public import Silmaril.Wasm.Logic.Hoare.Defs
public import Silmaril.Wasm.Game.Instantiate.Defs
public import Silmaril.Wasm.Logic.Memory.Defs
public import Silmaril.Wasm.Logic.Words.Defs

/-!
# An RV64 simulator in Wasm with the register file in linear memory (representation M)

`simM` is a Core 3.0 module (written with `wat3!`) exporting one memory `state` and one function
`step : [] → [i32]` that **fetches** a 32-bit instruction word from its own memory at the
simulated `pc`, **decodes** it and **executes** it, for all 21 instructions of the reference
model (`Silmaril.Sim.RV64.Ref`). The state lives in linear memory (`docs/projects/wasm-sim-abi.md`,
representation M):

| bytes | content |
|---|---|
| `[0, 8)` | `pc` (slot 0 of Linux riscv `struct user_regs_struct`) |
| `[8 r, 8 r + 8)` | `x_r`, `r = 1‥31` (`ra sp gp tp t0 …`, the same struct) |
| `[256, 264)` | valid mask (unused by `step`) |
| `[264, 272)` | `code_end`: fetch is allowed in `[0x1000, code_end)`, `code_end ≤ 0x10000` |
| `[0x1000, code_end)` | the program (P-data: code in the simulator's own memory) |

Status: `0` retired, `2` undecodable (outside the reference decoder), `3` fetch fault
(misaligned `pc`, `pc` outside `[0x1000, code_end)`, or `code_end > 0x10000`). On `2` and `3`
the memory is unchanged.

The code uses only what `Silmaril.Wasm.Logic.Core.exec1` evaluates (no conversions: the word is
loaded twice, as `i32` for register indices and as `i64.load32_u` for immediates; register
`x0` reads as `0` by `select`), so `wpc`/`wat_vc` apply. The abstraction (`absState`, `absCode`)
maps the memory bytes to the reference state and code. A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Sim.RV64.Mem

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game
open Silmaril.RiscV Silmaril.Sim.RV64

/-- **The simulator**, representation M, program in its own memory. -/
def simM : Module := wat3! r#"
(module
  (memory (export "state") 1)
  (func $step (export "step") (result i32)
    (local $pc i64) (local $end i64) (local $w i32) (local $w64 i64) (local $rd i32)
    (local $a i64) (local $b i64) (local $v i64)
    (local.set $pc (i64.load (i32.const 0)))
    (local.set $end (i64.load (i32.const 264)))
    (if (i64.ne (i64.rem_u (local.get $pc) (i64.const 4)) (i64.const 0))
      (then (return (i32.const 3))))
    (if (i64.lt_u (local.get $pc) (i64.const 4096)) (then (return (i32.const 3))))
    (if (i64.gt_u (local.get $end) (i64.const 65536)) (then (return (i32.const 3))))
    (if (i64.gt_u (local.get $pc) (i64.const 65532)) (then (return (i32.const 3))))
    (if (i64.gt_u (i64.add (local.get $pc) (i64.const 4)) (local.get $end))
      (then (return (i32.const 3))))
    (local.set $w (i32.load (i32.load (i32.const 0))))
    (local.set $w64 (i64.load32_u (i32.load (i32.const 0))))
    (local.set $rd (i32.rem_u (i32.shr_u (local.get $w) (i32.const 7)) (i32.const 32)))
    (local.set $a (select (i64.const 0)
      (i64.load (i32.mul (i32.rem_u (i32.shr_u (local.get $w) (i32.const 15)) (i32.const 32)) (i32.const 8))) (i32.eqz (i32.rem_u (i32.shr_u (local.get $w) (i32.const 15)) (i32.const 32)))))
    (local.set $b (select (i64.const 0)
      (i64.load (i32.mul (i32.rem_u (i32.shr_u (local.get $w) (i32.const 20)) (i32.const 32)) (i32.const 8))) (i32.eqz (i32.rem_u (i32.shr_u (local.get $w) (i32.const 20)) (i32.const 32)))))
    (block $exec
        (if (i32.eq (i32.rem_u (local.get $w) (i32.const 128)) (i32.const 19)) (then
          (if (i32.eq (i32.rem_u (i32.shr_u (local.get $w) (i32.const 12)) (i32.const 8)) (i32.const 0)) (then
            (local.set $v (i64.add (local.get $a) (i64.shr_s (i64.shl (local.get $w64) (i64.const 32)) (i64.const 52)))) (br $exec)))
          (if (i32.eq (i32.rem_u (i32.shr_u (local.get $w) (i32.const 12)) (i32.const 8)) (i32.const 2)) (then
            (local.set $v (select (i64.const 1) (i64.const 0) (i64.lt_s (local.get $a) (i64.shr_s (i64.shl (local.get $w64) (i64.const 32)) (i64.const 52))))) (br $exec)))
          (if (i32.eq (i32.rem_u (i32.shr_u (local.get $w) (i32.const 12)) (i32.const 8)) (i32.const 3)) (then
            (local.set $v (select (i64.const 1) (i64.const 0) (i64.lt_u (local.get $a) (i64.shr_s (i64.shl (local.get $w64) (i64.const 32)) (i64.const 52))))) (br $exec)))
          (if (i32.eq (i32.rem_u (i32.shr_u (local.get $w) (i32.const 12)) (i32.const 8)) (i32.const 4)) (then
            (local.set $v (i64.xor (local.get $a) (i64.shr_s (i64.shl (local.get $w64) (i64.const 32)) (i64.const 52)))) (br $exec)))
          (if (i32.eq (i32.rem_u (i32.shr_u (local.get $w) (i32.const 12)) (i32.const 8)) (i32.const 6)) (then
            (local.set $v (i64.or (local.get $a) (i64.shr_s (i64.shl (local.get $w64) (i64.const 32)) (i64.const 52)))) (br $exec)))
          (if (i32.eq (i32.rem_u (i32.shr_u (local.get $w) (i32.const 12)) (i32.const 8)) (i32.const 7)) (then
            (local.set $v (i64.and (local.get $a) (i64.shr_s (i64.shl (local.get $w64) (i64.const 32)) (i64.const 52)))) (br $exec)))
          (if (i32.eq (i32.rem_u (i32.shr_u (local.get $w) (i32.const 12)) (i32.const 8)) (i32.const 1)) (then
            (if (i32.eq (i32.shr_u (local.get $w) (i32.const 26)) (i32.const 0)) (then
              (local.set $v (i64.shl (local.get $a) (i64.rem_u (i64.shr_u (local.get $w64) (i64.const 20)) (i64.const 64)))) (br $exec)))
            ))
          (if (i32.eq (i32.rem_u (i32.shr_u (local.get $w) (i32.const 12)) (i32.const 8)) (i32.const 5)) (then
            (if (i32.eq (i32.shr_u (local.get $w) (i32.const 26)) (i32.const 0)) (then
              (local.set $v (i64.shr_u (local.get $a) (i64.rem_u (i64.shr_u (local.get $w64) (i64.const 20)) (i64.const 64)))) (br $exec)))
            (if (i32.eq (i32.shr_u (local.get $w) (i32.const 26)) (i32.const 16)) (then
              (local.set $v (i64.shr_s (local.get $a) (i64.rem_u (i64.shr_u (local.get $w64) (i64.const 20)) (i64.const 64)))) (br $exec)))
            ))
          (return (i32.const 2))))
        (if (i32.eq (i32.rem_u (local.get $w) (i32.const 128)) (i32.const 51)) (then
          (if (i32.eq (i32.shr_u (local.get $w) (i32.const 25)) (i32.const 0)) (then
            (if (i32.eq (i32.rem_u (i32.shr_u (local.get $w) (i32.const 12)) (i32.const 8)) (i32.const 0)) (then
              (local.set $v (i64.add (local.get $a) (local.get $b))) (br $exec)))
            (if (i32.eq (i32.rem_u (i32.shr_u (local.get $w) (i32.const 12)) (i32.const 8)) (i32.const 1)) (then
              (local.set $v (i64.shl (local.get $a) (local.get $b))) (br $exec)))
            (if (i32.eq (i32.rem_u (i32.shr_u (local.get $w) (i32.const 12)) (i32.const 8)) (i32.const 2)) (then
              (local.set $v (select (i64.const 1) (i64.const 0) (i64.lt_s (local.get $a) (local.get $b)))) (br $exec)))
            (if (i32.eq (i32.rem_u (i32.shr_u (local.get $w) (i32.const 12)) (i32.const 8)) (i32.const 3)) (then
              (local.set $v (select (i64.const 1) (i64.const 0) (i64.lt_u (local.get $a) (local.get $b)))) (br $exec)))
            (if (i32.eq (i32.rem_u (i32.shr_u (local.get $w) (i32.const 12)) (i32.const 8)) (i32.const 4)) (then
              (local.set $v (i64.xor (local.get $a) (local.get $b))) (br $exec)))
            (if (i32.eq (i32.rem_u (i32.shr_u (local.get $w) (i32.const 12)) (i32.const 8)) (i32.const 5)) (then
              (local.set $v (i64.shr_u (local.get $a) (local.get $b))) (br $exec)))
            (if (i32.eq (i32.rem_u (i32.shr_u (local.get $w) (i32.const 12)) (i32.const 8)) (i32.const 6)) (then
              (local.set $v (i64.or (local.get $a) (local.get $b))) (br $exec)))
            (if (i32.eq (i32.rem_u (i32.shr_u (local.get $w) (i32.const 12)) (i32.const 8)) (i32.const 7)) (then
              (local.set $v (i64.and (local.get $a) (local.get $b))) (br $exec)))
            ))
          (if (i32.eq (i32.shr_u (local.get $w) (i32.const 25)) (i32.const 32)) (then
            (if (i32.eq (i32.rem_u (i32.shr_u (local.get $w) (i32.const 12)) (i32.const 8)) (i32.const 0)) (then
              (local.set $v (i64.sub (local.get $a) (local.get $b))) (br $exec)))
            (if (i32.eq (i32.rem_u (i32.shr_u (local.get $w) (i32.const 12)) (i32.const 8)) (i32.const 5)) (then
              (local.set $v (i64.shr_s (local.get $a) (local.get $b))) (br $exec)))
            ))
          (return (i32.const 2))))
        (if (i32.eq (i32.rem_u (local.get $w) (i32.const 128)) (i32.const 55)) (then
          (local.set $v (i64.shl (i64.shr_s (i64.shl (local.get $w64) (i64.const 32)) (i64.const 44)) (i64.const 12))) (br $exec)))
        (if (i32.eq (i32.rem_u (local.get $w) (i32.const 128)) (i32.const 23)) (then
          (local.set $v (i64.add (local.get $pc) (i64.shl (i64.shr_s (i64.shl (local.get $w64) (i64.const 32)) (i64.const 44)) (i64.const 12)))) (br $exec)))
        (return (i32.const 2)))
    (if (local.get $rd) (then
      (i64.store (i32.mul (local.get $rd) (i32.const 8)) (local.get $v))))
    (i64.store (i32.const 0) (i64.add (local.get $pc) (i64.const 4)))
    (i32.const 0)))
"#

/-- The function `step`. -/
def stepFunc : Func := simM.funcs[0]

/-! ## The abstraction -/

/-- The little-endian `u64` at byte `a` (of the bytes present). -/
def ld64 (B : ByteArray) (a : Nat) : Word :=
  BitVec.ofNat 64 (Silmaril.Wasm.Logic.Core.leNat (Silmaril.Wasm.Logic.Core.bytesAt B ⟨a, 8⟩))

/-- The little-endian `u32` at byte `a` (of the bytes present). -/
def ld32 (B : ByteArray) (a : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (Silmaril.Wasm.Logic.Core.leNat (Silmaril.Wasm.Logic.Core.bytesAt B ⟨a, 4⟩))

/-- The reference register state held by the memory bytes `B`: `pc` at byte `0`, `x_r` at byte
`8 r` (`x0` reads as zero; its slot is `pc`'s). -/
def absState (B : ByteArray) : State where
  regs r := if r = 0#5 then 0 else ld64 B (8 * r.toNat)
  pc := ld64 B 0

/-- The end of the code region. -/
def codeEnd (B : ByteArray) : Nat := (ld64 B 264).toNat

/-- The code held by `B`: the word at `pc` when `pc` is four-byte aligned and
`0x1000 ≤ pc`, `pc + 4 ≤ code_end ≤ 0x10000`. -/
def absCode (B : ByteArray) : Silmaril.Sim.RV64.Code := fun pc =>
  if pc.toNat % 4 = 0 ∧ 4096 ≤ pc.toNat ∧ pc.toNat + 4 ≤ codeEnd B ∧ codeEnd B ≤ 65536 then
    some (ld32 B pc.toNat)
  else none

/-- `B` is a well-formed simulator memory: at least one page. -/
def WF (B : ByteArray) : Prop := 65536 ≤ B.size

/-! ## Loading a reference state and a program -/

/-- Slot `r` of the register block: `pc` for `r = 0`, else `x_r`. -/
def slotVal (σ : State) (r : Nat) : Word := if r = 0 then σ.pc else σ.regs (BitVec.ofNat 5 r)

/-- Byte `k` (little-endian) of `v`. -/
def byteOf (v k : Nat) : UInt8 := UInt8.ofNat (v / 2 ^ (8 * k))

/-- Byte `i` of the memory image of `σ` with the program `ws` at `0x1000`. -/
def imgByte (σ : State) (ws : List (BitVec 32)) (i : Nat) : UInt8 :=
  if i < 256 then byteOf (slotVal σ (i / 8)).toNat (i % 8)
  else if 264 ≤ i ∧ i < 272 then byteOf (4096 + 4 * ws.length) (i - 264)
  else if 4096 ≤ i ∧ i < 4096 + 4 * ws.length then
    byteOf (ws.getD ((i - 4096) / 4) 0).toNat ((i - 4096) % 4)
  else 0

/-- **The memory image** (one page) holding the reference state `σ` and the program `ws` at
`0x1000`, with `code_end = 0x1000 + 4 |ws|`. -/
def img (σ : State) (ws : List (BitVec 32)) : ByteArray :=
  ⟨((List.range 65536).map (imgByte σ ws)).toArray⟩

/-! ## The specification of `step` -/

/-- What one call of `step` does to the memory bytes `B`, returning the status `st` and leaving
`B'`: status `0` retires exactly one reference step (`refStep`) on the abstraction and changes
no byte outside the register block `[0, 256)`; status `2` or `3` leaves the memory unchanged
and the reference machine **stops** there (fetch fault or undecodable word). -/
def StepPost (B : ByteArray) (st : BitVec 32) (B' : ByteArray) : Prop :=
  (st = 0 ∧ refStep (absCode B) (absState B) = some (absState B') ∧
      Silmaril.Wasm.Logic.Words.SameOutside B B' 0 256) ∨
  ((st = 2 ∨ st = 3) ∧ B' = B ∧ refStep (absCode B) (absState B) = none)

variable {H : Type}

/-- **The specification of `step`** at function address `a` (instance `fi`), whose memory `0`
is the store's memory `ma` of type `mt` holding `B`: the call returns one `i32` status `st`, the
store differs only in that memory, now holding `B'`, and `StepPost B st B'`. -/
def stepSpec (fi : FuncInst H) (a ma : Nat) (mt : MemoryType) (B : ByteArray) :
    Silmaril.Wasm.Logic.Hoare.FSpec H where
  pre s args := s.funcs[a]? = some fi ∧ args = [] ∧
    Silmaril.Wasm.Logic.Words.MemAt s fi.module ma mt B ∧ WF B
  post s _ s' o := ∃ (st : BitVec 32) (B' : ByteArray),
    o = .normal [.num ⟨.int .i32, st⟩] ∧ s' = s.setMem ma ⟨mt, B'⟩ ∧ StepPost B st B'

end Silmaril.Sim.RV64.Mem
