module

public import Silmaril.Proofs.Sim.X86.Toy.Steps
public import Silmaril.Sim.X86.GM.Thms

/-!
# The toy `f`: the Wasm problem, solved with the dispatcher's cut-point rule

`CP`: one assertion per cut point (the 23 instructions of `toyTab` and the exit at the caller's
return address) on the store's registers and Wasm memory slots (offsets `32` caller's return
address, `24` saved `rbx`, `16` saved `r12`, `0` the inner calls' return addresses), with a
measure `k` that every entry decreases. **`toy_step_all`**: every entry of the dispatcher, from
a `CP`-store, evaluates to a `CP`-store of smaller measure, or the exit holds the postcondition:
the hypothesis of both `dispatch_hwp` (`wasm_solution`, partial correctness) and `xrun_existsM`
(termination, `Silmaril.Proofs.Sim.X86.Toy.X86`).
-/

@[expose] public section

namespace Silmaril.Sim.X86.Toy

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.X86 (Reg Word)
open Silmaril.Sim.X86.G Silmaril.Sim.X86.GM Silmaril.Sim.X86.Loop
open Silmaril.Sim.X86.SumTo (tri tri_step b64_xor_one)
open Silmaril.Wasm.Logic.Core (exec Post)

variable {H : Type} {s : Store H} {f : Frame}

/-- A Wasm memory slot. -/
abbrev Ld (B : ByteArray) (o : Nat) (v : Word) : Prop := Memory.load B o 8 = some v

/-- **The cut points of `f`** at code base `b`, stack pointer `sp` on entry, initial registers
`R`, caller's return address `ret`, with measure `k`. -/
def CP (b sp ret : Word) (R : Reg → Word) (k : Nat) (ip ax di rsp bx r12 zf : Word)
    (B : ByteArray) : Prop :=
  let N := R .rdi; let M := R .rsi; let T := BitVec.ofNat 64 (tri N.toNat)
  let Sv := Ld B 24 (R .rbx) ∧ Ld B 16 (R .r12)
  Ld B 32 ret ∧ (
  -- f, before the first call
  (ip = b + 0x1d ∧ rsp = sp ∧ bx = R .rbx ∧ r12 = R .r12 ∧ di = N ∧ k = 5 * N.toNat + 29) ∨
  (ip = b + 0x1e ∧ rsp = sp - 8 ∧ bx = R .rbx ∧ r12 = R .r12 ∧ di = N ∧ Ld B 24 (R .rbx) ∧
    k = 5 * N.toNat + 28) ∨
  (ip = b + 0x20 ∧ rsp = sp - 16 ∧ bx = R .rbx ∧ r12 = R .r12 ∧ di = N ∧ Sv ∧
    k = 5 * N.toNat + 27) ∨
  (ip = b + 0x24 ∧ rsp = sp - 24 ∧ bx = R .rbx ∧ r12 = R .r12 ∧ di = N ∧ Sv ∧
    k = 5 * N.toNat + 26) ∨
  (ip = b + 0x27 ∧ rsp = sp - 24 ∧ bx = M ∧ r12 = R .r12 ∧ di = N ∧ Sv ∧ k = 5 * N.toNat + 25) ∨
  -- sum_to
  (rsp = sp - 32 ∧ bx = M ∧ r12 = R .r12 ∧ Sv ∧ Ld B 0 (b + 0x2c) ∧ (
    (ip = b ∧ di = N ∧ k = 5 * N.toNat + 24) ∨
    (ip = b + 0x07 ∧ di.toNat ≤ N.toNat ∧ ax = BitVec.ofNat 64 (tri N.toNat - tri di.toNat) ∧
      k = 5 * di.toNat + 23) ∨
    (ip = b + 0x0a ∧ di.toNat ≤ N.toNat ∧ ax = BitVec.ofNat 64 (tri N.toNat - tri di.toNat) ∧
      zf = b64 (di == 0) ∧ k = 5 * di.toNat + 22) ∨
    (ip = b + 0x0c ∧ di ≠ 0 ∧ di.toNat ≤ N.toNat ∧
      ax = BitVec.ofNat 64 (tri N.toNat - tri di.toNat) ∧ k = 5 * di.toNat + 21) ∨
    (ip = b + 0x0f ∧ di ≠ 0 ∧ di.toNat ≤ N.toNat ∧
      ax = BitVec.ofNat 64 (tri N.toNat - tri di.toNat) + di ∧ k = 5 * di.toNat + 20) ∨
    (ip = b + 0x13 ∧ di.toNat < N.toNat ∧ ax = BitVec.ofNat 64 (tri N.toNat - tri di.toNat) ∧
      k = 5 * di.toNat + 24) ∨
    (ip = b + 0x15 ∧ ax = T ∧ k = 21))) ∨
  -- f, between the calls
  (ip = b + 0x2c ∧ rsp = sp - 24 ∧ ax = T ∧ bx = M ∧ r12 = R .r12 ∧ Sv ∧ k = 15) ∨
  (ip = b + 0x2f ∧ rsp = sp - 24 ∧ bx = M ∧ r12 = T ∧ Sv ∧ k = 14) ∨
  (ip = b + 0x32 ∧ rsp = sp - 24 ∧ di = M ∧ r12 = T ∧ Sv ∧ k = 13) ∨
  -- dbl
  (rsp = sp - 32 ∧ di = M ∧ r12 = T ∧ Sv ∧ Ld B 0 (b + 0x37) ∧ (
    (ip = b + 0x16 ∧ k = 12) ∨ (ip = b + 0x19 ∧ ax = M ∧ k = 11) ∨
    (ip = b + 0x1c ∧ ax = M + M ∧ k = 10))) ∨
  -- f, after the calls
  (ip = b + 0x37 ∧ rsp = sp - 24 ∧ ax = M + M ∧ r12 = T ∧ Sv ∧ k = 9) ∨
  (ip = b + 0x3a ∧ rsp = sp - 24 ∧ ax = M + M + T ∧ Sv ∧ k = 8) ∨
  (ip = b + 0x3e ∧ rsp = sp - 16 ∧ ax = M + M + T ∧ Sv ∧ k = 7) ∨
  (ip = b + 0x40 ∧ rsp = sp - 8 ∧ ax = M + M + T ∧ r12 = R .r12 ∧ Ld B 24 (R .rbx) ∧ k = 6) ∨
  (ip = b + 0x41 ∧ rsp = sp ∧ ax = M + M + T ∧ r12 = R .r12 ∧ bx = R .rbx ∧ k = 5) ∨
  -- returned
  (ip = ret ∧ rsp = sp + 8 ∧ ax = M + M + T ∧ r12 = R .r12 ∧ bx = R .rbx))

/-- The measured invariant on stores. -/
def JT (b sp ret : Word) (f : Frame) (R : Reg → Word) (k : Nat) (s : Store H) : Prop :=
  ∃ ip ax di rsp bx r12 zf B, TV s f R ip ax di rsp bx r12 zf B ∧
    CP b sp ret R k ip ax di rsp bx r12 zf B

end Silmaril.Sim.X86.Toy

namespace Silmaril.Sim.X86.Toy

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.X86 (Reg Word)
open Silmaril.Sim.X86.G Silmaril.Sim.X86.GM Silmaril.Sim.X86.Loop
open Silmaril.Sim.X86.SumTo (tri tri_step b64_xor_one)
open Silmaril.Wasm.Logic.Core (exec Post exec_cons exec_nil)

variable {H : Type} {s : Store H} {f : Frame}

/-- The exit condition: returned to `ret` with the result. -/
def QT (sp ret : Word) (R : Reg → Word) : Post H := fun s f o =>
  o = .normal [] ∧ ∃ di zf B, TV s f R ret
    (R .rsi + R .rsi + BitVec.ofNat 64 (tri (R .rdi).toNat)) di (sp + 8) (R .rbx) (R .r12) zf B

section Arith

variable {sp : Word}

theorem toyWin_ok (h32 : 32 ≤ sp.toNat) (h8 : sp.toNat + 8 ≤ 2 ^ 64) : (toyWin sp).Ok := by
  refine ⟨by simp [toyWin], by simp [toyWin], ?_⟩
  simp only [toyWin]; bv_omega

theorem holds_sp (h32 : 32 ≤ sp.toNat) (h8 : sp.toNat + 8 ≤ 2 ^ 64) (c : Word)
    (hc : c.toNat ≤ 32) : (toyWin sp).Holds (sp - c) := by
  simp only [Win.Holds, toyWin]; bv_omega

theorem off_sp (h32 : 32 ≤ sp.toNat) (c : Word) (hc : c.toNat ≤ 32) :
    (sp - c).toNat - (toyWin sp).lo.toNat = 32 - c.toNat := by
  simp only [toyWin]; bv_omega

end Arith

theorem ld_same {B B' : ByteArray} {o : Nat} {v : Word}
    (h : Memory.store B o (count := 8) v = some B') : Ld B' o v :=
  Silmaril.Wasm.Logic.Core.load_store_same h

theorem ld_keep {B B' : ByteArray} {o o' : Nat} {v w : Word}
    (h : Memory.store B o (count := 8) v = some B') (hd : o + 8 ≤ o' ∨ o' + 8 ≤ o)
    (hw : Ld B o' w) : Ld B' o' w := by
  show Memory.load B' o' 8 = _
  rw [Silmaril.Wasm.Logic.Core.load_store_disjoint h (by
    simp only [Silmaril.Wasm.Logic.Core.Region.Disjoint, Silmaril.Wasm.Logic.Core.Region.stop]; omega)]
  exact hw

theorem size_keep {B B' : ByteArray} {o : Nat} {v : Word}
    (h : Memory.store B o (count := 8) v = some B') : B'.size = B.size :=
  Silmaril.Wasm.Logic.Core.size_store h

end Silmaril.Sim.X86.Toy
