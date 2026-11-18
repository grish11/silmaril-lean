module

public import Silmaril.Sim.X86.GM.Defs
public import Silmaril.Sim.X86.G.Thms

/-!
# GM: evaluation of the address code

`exec1` lemmas for the `i32` and comparison instructions the memory code uses; **`exec_wrap`**:
`wrapCode X` pushes the low 32 bits of the `i64` that `X` computes (when `X` is pure).
-/

@[expose] public section

namespace Silmaril.Sim.X86.GM

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Sim.X86.G
open Silmaril.Wasm.Logic.Core (exec exec1 exec_cons exec_nil exec_append)

variable {H : Type} {s : Store H} {f : Frame}

theorem exec1_c32 (rs : List Val) (c : BitVec 32) :
    exec1 s f rs (c32 c) = some (s, f, Val.i32 c :: rs) := rfl

theorem exec1_shl32 (rs : List Val) (x y : BitVec 32) :
    exec1 s f (Val.i32 y :: Val.i32 x :: rs) (b32op .shl) =
      some (s, f, Val.i32 (x <<< (y.toNat % 32)) :: rs) := rfl

theorem exec1_add32 (rs : List Val) (x y : BitVec 32) :
    exec1 s f (Val.i32 y :: Val.i32 x :: rs) (b32op .add) = some (s, f, Val.i32 (x + y) :: rs) :=
  rfl

theorem exec1_ne64 (rs : List Val) (x y : BitVec 64) :
    exec1 s f (Val.i64 y :: Val.i64 x :: rs) (.intRelOp .i64 .ne) =
      some (s, f, Val.i32 (bool32 (x != y)) :: rs) := rfl

theorem exec1_leu64 (rs : List Val) (x y : BitVec 64) :
    exec1 s f (Val.i64 y :: Val.i64 x :: rs) (.intRelOp .i64 (.le .unsigned)) =
      some (s, f, Val.i32 (bool32 (decide (x.toNat ≤ y.toNat))) :: rs) := rfl

theorem exec1_div1 (rs : List Val) :
    exec1 s f (Val.i32 1 :: Val.i32 1 :: rs) (b32op (.div .unsigned)) =
      some (s, f, Val.i32 1 :: rs) := rfl

theorem exec1_div0 (rs : List Val) :
    exec1 s f (Val.i32 0 :: Val.i32 1 :: rs) (b32op (.div .unsigned)) = none := rfl

theorem exec1_drop (rs : List Val) (v : Val) : exec1 s f (v :: rs) .drop = some (s, f, rs) := rfl

theorem exec1_shr64 (rs : List Val) (x y : BitVec 64) :
    exec1 s f (Val.i64 y :: Val.i64 x :: rs) (b64op (.shr .unsigned)) =
      some (s, f, Val.i64 (x >>> (y.toNat % 64)) :: rs) := by
  rw [exec1_b64op]; rfl

/-- `X` computes the `i64` value `x` without changing the store, frame or stack below. -/
def Pure (s : Store H) (f : Frame) (X : List Instr) (x : BitVec 64) : Prop :=
  ∀ rs, exec s f rs X = some (s, f, Val.i64 x :: rs)

/-- The `i32` bit `k` of `x`, as `wrapStep` computes it. -/
theorem wrap_bit (x : BitVec 64) (k : Nat) (hk : k < 32) :
    (bool32 ((x >>> ((BitVec.ofNat 64 k).toNat % 64)) &&& 1 != 0) <<<
      ((BitVec.ofNat 32 k).toNat % 32)).toNat = (x.toNat / 2 ^ k) % 2 * 2 ^ k := by
  have hk1 : (BitVec.ofNat 64 k).toNat % 64 = k := by
    rw [BitVec.toNat_ofNat]; omega
  have hk2 : (BitVec.ofNat 32 k).toNat % 32 = k := by
    rw [BitVec.toNat_ofNat]; omega
  rw [hk1, hk2]
  have hb : ((x >>> k) &&& 1).toNat = (x.toNat / 2 ^ k) % 2 := by
    rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    simp [Nat.and_one_is_mod]
  have hlt : 2 ^ k < 2 ^ 32 := Nat.pow_lt_pow_right (by decide) hk
  rcases Nat.mod_two_eq_zero_or_one (x.toNat / 2 ^ k) with h | h
  · have : (x >>> k) &&& 1 = 0 := BitVec.eq_of_toNat_eq (by rw [hb, h]; rfl)
    rw [this, h]
    simp [bool32]
  · have : ((x >>> k) &&& 1 != 0) = true := by
      simp only [bne_iff_ne, ne_eq]
      intro e; rw [e] at hb; simp at hb; omega
    rw [this, h]
    simp only [bool32, ite_true, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, one_mul]
    rw [show (1 : BitVec 32).toNat = 1 from rfl, one_mul, Nat.mod_eq_of_lt hlt]

theorem exec_wrapAux {X : List Instr} {x : BitVec 64} (hX : Pure s f X x) (rs : List Val) :
    ∀ k ≤ 32, exec s f (Val.i32 0 :: rs) (wrapAux X k) =
      some (s, f, Val.i32 (BitVec.ofNat 32 (x.toNat % 2 ^ k)) :: rs) := by
  intro k
  induction k with
  | zero => intro _; simp only [wrapAux, exec_nil, pow_zero, Nat.mod_one]; rfl
  | succ k ih =>
    show k + 1 ≤ 32 → exec s f (Val.i32 0 :: rs) (wrapAux X (k + 1)) =
      some (s, f, Val.i32 (BitVec.ofNat 32 (x.toNat % 2 ^ (k + 1))) :: rs)
    intro hk
    rw [wrapAux, exec_append, ih (by omega)]
    simp only
    rw [wrapStep, exec_append, hX]
    simp only [exec_cons, exec_nil, exec1_c64, exec1_shr64, exec1_and, exec1_ne64, exec1_c32,
      exec1_shl32, exec1_add32]
    refine congrArg (fun v => some (s, f, Val.i32 v :: rs)) ?_
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, wrap_bit x k (by omega), BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have h1 : x.toNat % 2 ^ k < 2 ^ 32 :=
      lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.pow_le_pow_right (by decide) (by omega))
    have h2 : x.toNat % 2 ^ (k + 1) < 2 ^ 32 :=
      lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.pow_le_pow_right (by decide) hk)
    have e : x.toNat % 2 ^ (k + 1) = x.toNat % 2 ^ k + x.toNat / 2 ^ k % 2 * 2 ^ k := by
      rw [Nat.mod_pow_succ, Nat.mul_comm]
    rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2, ← e, Nat.mod_eq_of_lt h2]

/-- **The `i32` wrap.** -/
theorem exec_wrap {X : List Instr} {x : BitVec 64} (hX : Pure s f X x) (rs : List Val) :
    exec s f rs (wrapCode X) = some (s, f, Val.i32 (x.setWidth 32) :: rs) := by
  rw [wrapCode, exec_append]
  simp only [exec_cons, exec_nil, exec1_c32]
  rw [exec_wrapAux hX rs 32 le_rfl]
  refine congrArg (fun v => some (s, f, Val.i32 v :: rs)) ?_
  apply BitVec.eq_of_toNat_eq
  simp

end Silmaril.Sim.X86.GM
