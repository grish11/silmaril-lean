module

public import Silmaril.Proofs.Sim.X86.GM.Mem
public import Silmaril.Sim.X86.G.Thms

/-!
# GM: evaluation of checked loads and stores

`Pure` address/value code (`pure_gget`, `pure_addr`, `pure_rspDown`, …); **`exec_check`** (the
window check passes exactly for accesses in the window), **`exec_load`**, **`exec_store`**
(checked accesses agree with `Ext.loadN`/`Ext.storeN`); `popWord_loadN`, `pushWord_storeN`
(the stack accesses are 8-byte loads and stores).
-/

@[expose] public section

namespace Silmaril.Sim.X86.GM

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.X86 (Reg Word State)
open Silmaril.X86.Ext (Mem Base Index)
open Silmaril.Sim.X86.G
open Silmaril.Wasm.Logic.Core (exec exec1 exec_cons exec_nil exec_append)

variable {H : Type} {s : Store H} {f : Frame}

theorem pure_gget {l : Loc} {v : Word} (h : gval s f l = some (Val.i64 v)) : Pure s f [gget l] v :=
  fun rs => by simp only [exec_cons, exec_nil, exec1_gget, h, Option.map_some]

theorem pure_c64 (c : Word) : Pure s f [c64 c] c := fun _ => rfl

theorem Pure.op {X Y : List Instr} {x y : Word} (hX : Pure s f X x) (hY : Pure s f Y y)
    (op : IntBinOp) {z : Word} (hz : intBinOp .i64 op x y = .ok z) :
    Pure s f (X ++ Y ++ [b64op op]) z := fun rs => by
  rw [exec_append, exec_append, hX]
  simp only
  rw [hY]
  simp only [exec_cons, exec_nil, exec1_b64op, hz]

theorem pure_off {W : Win} {X : List Instr} {x : Word} (hX : Pure s f X x) :
    Pure s f (offCode W X) (x - W.lo) := by
  have := hX.op (pure_c64 W.lo) .sub (z := x - W.lo) rfl
  rw [List.append_assoc] at this
  exact this

theorem pure_rspDown {σ : State} (hE : Enc s f σ) : Pure s f rspDown (σ.read .rsp - 8#64) :=
  (pure_gget (hE.2.1 .rsp)).op (pure_c64 8) .sub (z := σ.read .rsp - 8#64) rfl

theorem pure_addr {σ : State} (hE : Enc s f σ) {m : Mem} (hp : plainMem m = true) (next : Word) :
    Pure s f (addrCode m) (m.addr σ next) := by
  obtain ⟨base, index, disp, hrip⟩ := m
  have hb : Pure s f (baseCode base) (Base.value base σ next) := by
    cases base with
    | reg b => exact pure_gget (hE.2.1 b)
    | none => exact pure_c64 0
    | rip => exact absurd hp (by simp [plainMem])
    | fs => exact absurd hp (by simp [plainMem])
  have hi : ∀ rs (y : Word), exec s f (Val.i64 y :: rs) (indexCode index) = some (s, f, Val.i64 (y + (index.map fun i => i.value σ).getD 0#64) :: rs) := by
    intro rs y
    cases index with
    | none => simp [indexCode]
    | some i =>
      show exec s f (Val.i64 y :: rs) (indexCode (some i)) =
        some (s, f, Val.i64 (y + i.value σ) :: rs)
      simp only [indexCode]
      have hs : (BitVec.ofNat 64 i.scale.toNat).toNat % 64 = i.scale.toNat := by
        have hlt : i.scale.toNat < 2 ^ 2 := i.scale.isLt
        rw [BitVec.toNat_ofNat]; omega
      have hshl : intBinOp .i64 .shl (σ.read i.reg) (BitVec.ofNat 64 i.scale.toNat) =
          .ok (σ.read i.reg <<< i.scale.toNat) := by
        simp only [intBinOp, IntType.width, hs]; rfl
      simp only [exec_cons, exec_nil, exec1_gget, hE.2.1 i.reg, Option.map_some, exec1_c64]
      rw [exec1_b64op, hshl]
      simp only [exec1_add, Index.value]
  intro rs
  have hbi : exec s f rs (baseCode base ++ indexCode index) =
      some (s, f, Val.i64 (Base.value base σ next + (index.map fun i => i.value σ).getD 0#64) :: rs) := by
    rw [exec_append, hb rs]
    exact hi rs _
  show exec s f rs (addrCode ⟨base, index, disp, hrip⟩) = _
  simp only [addrCode]
  rw [exec_append, hbi]
  simp only [exec_cons, exec_nil, exec1_c64, exec1_add, Mem.addr]

/-! ## The check -/

instance (W : Win) (a : Word) : Decidable (W.Holds a) := inferInstanceAs (Decidable (_ ∧ _))
instance (W : Win) (k : Nat) (a : Word) : Decidable (W.HoldsK k a) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem holds_iffK {W : Win} {k : Nat} (hk0 : 0 < k) (hk : k ≤ W.size) (h32 : W.size ≤ 2 ^ 32)
    (hlim : W.lo.toNat + W.size ≤ 2 ^ 64) (x : Word) :
    W.HoldsK k x ↔ (x - W.lo).toNat ≤ (BitVec.ofNat 64 (W.size - k)).toNat := by
  rw [BitVec.toNat_ofNat, BitVec.toNat_sub, Nat.mod_eq_of_lt (by omega : W.size - k < 2 ^ 64)]
  have := x.isLt; have := W.lo.isLt
  simp only [Win.HoldsK]
  constructor
  · rintro ⟨h1, h2⟩; rw [show 2 ^ 64 - W.lo.toNat + x.toNat = (x.toNat - W.lo.toNat) + 2 ^ 64 by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega
  · intro h
    by_cases h1 : W.lo.toNat ≤ x.toNat
    · rw [show 2 ^ 64 - W.lo.toNat + x.toNat = (x.toNat - W.lo.toNat) + 2 ^ 64 by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at h
      omega
    · rw [Nat.mod_eq_of_lt (by omega)] at h; omega

/-- **The window check** of a `k`-byte access. -/
theorem exec_checkK {W : Win} {k : Nat} (hk0 : 0 < k) {X : List Instr} {x : Word}
    (hX : Pure s f X x) (h32 : W.size ≤ 2 ^ 32) (hlim : W.lo.toNat + W.size ≤ 2 ^ 64) (rs : List Val) :
    exec s f rs (checkCodeK W k X) = if W.HoldsK k x then some (s, f, rs) else none := by
  by_cases hk : k ≤ W.size
  · rw [checkCodeK, ite_eq_left_of_eq_true _ _ (eq_true hk), exec_append, exec_append]
    simp only [exec_cons, exec_nil, exec1_c32]
    rw [pure_off hX]
    simp only [exec1_c64, exec1_leu64]
    by_cases hh : W.HoldsK k x
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hh), show decide ((x - W.lo).toNat ≤
          (BitVec.ofNat 64 (W.size - k)).toNat) = true
        from decide_eq_true ((holds_iffK hk0 hk h32 hlim x).mp hh)]
      rfl
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hh), show decide ((x - W.lo).toNat ≤
          (BitVec.ofNat 64 (W.size - k)).toNat) = false
        from decide_eq_false (fun h => hh ((holds_iffK hk0 hk h32 hlim x).mpr h))]
      rfl
  · have hh : ¬ W.HoldsK k x := fun ⟨h1, h2⟩ => hk (by omega)
    rw [checkCodeK, ite_eq_right_of_eq_false _ _ (eq_false hk), ite_eq_right_of_eq_false _ _ (eq_false hh)]
    rfl

/-- **The window check.** -/
theorem exec_check {W : Win} {X : List Instr} {x : Word} (hX : Pure s f X x)
    (h32 : W.size ≤ 2 ^ 32) (hlim : W.lo.toNat + W.size ≤ 2 ^ 64) (rs : List Val) :
    exec s f rs (checkCode W X) = if W.Holds x then some (s, f, rs) else none :=
  exec_checkK (k := 8) (by omega) hX h32 hlim rs

/-- The translated `i32` address. -/
theorem exec_waddr {W : Win} {X : List Instr} {x : Word} (hX : Pure s f X x) (rs : List Val) :
    exec s f rs (wrapCode (offCode W X)) = some (s, f, Val.i32 ((x - W.lo).setWidth 32) :: rs) :=
  exec_wrap (pure_off hX) rs

/-- **A checked load in the window.** -/
theorem exec_load {mem : Silmaril.Process.Memory} {W : Win} (hM : MemEnc s f mem W)
    {X : List Instr} {x : Word} (hX : Pure s f X x) (hh : W.Holds x) (rs : List Val) :
    ∃ v, Silmaril.X86.Ext.loadN mem x 8 = some v ∧
      exec s f rs (loadCode W X) = some (s, f, Val.i64 v :: rs) := by
  obtain ⟨B₀, -, -, h32, hlim, -⟩ := id hM
  obtain ⟨B, v, hB, hx, hl⟩ := hM.load hh
  obtain ⟨ma, mi, hm, rfl⟩ := wbytes_eq hB
  refine ⟨v, hx, ?_⟩
  rw [loadCode, exec_append, exec_append, exec_check hX h32 hlim, ite_eq_left_of_eq_true _ _ (eq_true hh)]
  simp only
  rw [exec_waddr hX]
  simp only
  rw [← (off_toNat h32 hh).1] at hl
  simp only [exec_cons, exec_nil, exec1_load64 hm hl]

/-- The zero-extending `k`-byte load. -/
theorem exec1_ldK {ma : Nat} {mi : MemInst} (hm : s.mem? f ⟨0⟩ = some (ma, mi)) {k : Nat}
    (hk : k = 1 ∨ k = 2 ∨ k = 4 ∨ k = 8) {a : BitVec 32} {L : Nat}
    (hl : Memory.load mi.bytes a.toNat k = some (BitVec.ofNat (8 * k) L)) (rs : List Val) :
    exec1 s f (Val.i32 a :: rs) (ldK k) =
      some (s, f, Val.i64 ((BitVec.ofNat (8 * k) L).setWidth 64) :: rs) := by
  rcases hk with rfl | rfl | rfl | rfl <;>
  · simp only [ldK, exec1, Silmaril.Wasm.Logic.Core.popInt, Option.bind_some, hm, Val.i32]
    exact (congrArg (Option.map _) hl).trans rfl

/-- **A checked `k`-byte load in the window**: it pushes the zero-extended little-endian number
the x86 load reads. -/
theorem exec_loadK {mem : Silmaril.Process.Memory} {W : Win} (hM : MemEnc s f mem W) {k : Nat}
    (hk : k = 1 ∨ k = 2 ∨ k = 4 ∨ k = 8)
    {X : List Instr} {x : Word} (hX : Pure s f X x) (hh : W.HoldsK k x) :
    ∃ L, Silmaril.X86.Ext.loadN mem x k = some (BitVec.ofNat 64 L) ∧
      Pure s f (loadCodeK W k X) ((BitVec.ofNat (8 * k) L).setWidth 64) := by
  obtain ⟨B₀, -, -, h32, hlim, -⟩ := id hM
  obtain ⟨B, L, hB, hx, hl⟩ := hM.loadK hh
  obtain ⟨ma, mi, hm, rfl⟩ := wbytes_eq hB
  refine ⟨L, hx, fun rs => ?_⟩
  rw [loadCodeK, exec_append, exec_append, exec_checkK (by omega) hX h32 hlim,
    ite_eq_left_of_eq_true _ _ (eq_true hh)]
  simp only
  rw [exec_waddr hX]
  simp only
  rw [← (off_toNatK (by omega) h32 hh).1] at hl
  simp only [exec_cons, exec_nil, exec1_ldK hm hk hl]

/-- A checked `k`-byte load that evaluates is in the window. -/
theorem loadK_holds {W : Win} {k : Nat} (hk0 : 0 < k) {X : List Instr} {x : Word} (hX : Pure s f X x)
    (h32 : W.size ≤ 2 ^ 32) (hlim : W.lo.toNat + W.size ≤ 2 ^ 64) {rs : List Val}
    {r : Store H × Frame × List Val} (he : exec s f rs (loadCodeK W k X) = some r) :
    W.HoldsK k x := by
  by_contra hh
  rw [loadCodeK, exec_append, exec_append, exec_checkK hk0 hX h32 hlim,
    ite_eq_right_of_eq_false _ _ (eq_false hh)] at he
  cases he

/-- A checked load that evaluates is in the window. -/
theorem load_holds {W : Win} {X : List Instr} {x : Word} (hX : Pure s f X x)
    (h32 : W.size ≤ 2 ^ 32) (hlim : W.lo.toNat + W.size ≤ 2 ^ 64) {rs : List Val}
    {r : Store H × Frame × List Val} (he : exec s f rs (loadCode W X) = some r) : W.Holds x := by
  by_contra hh
  rw [loadCode, exec_append, exec_append, exec_check hX h32 hlim, ite_eq_right_of_eq_false _ _ (eq_false hh)] at he
  cases he

theorem store_holds {W : Win} {X V : List Instr} {x : Word} (hX : Pure s f X x)
    (h32 : W.size ≤ 2 ^ 32) (hlim : W.lo.toNat + W.size ≤ 2 ^ 64) {rs : List Val}
    {r : Store H × Frame × List Val} (he : exec s f rs (storeCode W X V) = some r) : W.Holds x := by
  by_contra hh
  rw [storeCode, exec_append, exec_append, exec_append, exec_check hX h32 hlim, ite_eq_right_of_eq_false _ _ (eq_false hh)] at he
  cases he

/-- **A checked store in the window.** -/
theorem exec_store {mem : Silmaril.Process.Memory} {W : Win} (hM : MemEnc s f mem W)
    (hrw : W.rw = true) {X V : List Instr} {x v : Word} (hX : Pure s f X x) (hV : Pure s f V v)
    (hh : W.Holds x) (rs : List Val) :
    ∃ (ma : Nat) (mi : MemInst) (B' : ByteArray) (mem' : Silmaril.Process.Memory),
      Silmaril.X86.Ext.storeN mem x 8 v = some mem' ∧
      exec s f rs (storeCode W X V) = some (s.setMem ma { mi with bytes := B' }, f, rs) ∧
      MemEnc (s.setMem ma { mi with bytes := B' }) f mem' W ∧ mem.WritesWithin mem' W.Mem := by
  obtain ⟨B₀, -, -, h32, hlim, -⟩ := id hM
  obtain ⟨ma, mi, B', mem', hm, hx, hst, hM', hw⟩ := hM.store hrw hh v
  refine ⟨ma, mi, B', mem', hx, ?_, hM', hw⟩
  rw [storeCode, exec_append, exec_append, exec_append, exec_check hX h32 hlim, ite_eq_left_of_eq_true _ _ (eq_true hh)]
  simp only
  rw [exec_waddr hX]
  simp only
  rw [hV]
  simp only
  rw [← (off_toNat h32 hh).1] at hst
  simp only [exec_cons, exec_nil, exec1_store64 hm hst]

/-! ## The stack -/

theorem or_byte (a b : Nat) (hb : b < 2 ^ 8) : a * 2 ^ 8 ||| b = a * 256 + b := by
  rw [Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt hb]; omega

theorem wordOfBytes?_eq (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    Silmaril.X86.wordOfBytes? [b0, b1, b2, b3, b4, b5, b6, b7] =
      some (BitVec.ofNat 64 (Silmaril.X86.Ext.leValue [b0, b1, b2, b3, b4, b5, b6, b7])) := by
  simp only [Silmaril.X86.wordOfBytes?, Option.some.injEq]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_append, Silmaril.X86.Ext.leValue, BitVec.toNat_ofNat]
  have := b0.isLt; have := b1.isLt; have := b2.isLt; have := b3.isLt
  have := b4.isLt; have := b5.isLt; have := b6.isLt; have := b7.isLt
  simp only [Nat.shiftLeft_eq, or_byte _ _ (BitVec.isLt _)]
  omega

theorem popWord_loadN {σ : State} {mem : Silmaril.Process.Memory} {v : Word}
    (h : Silmaril.X86.Ext.loadN mem (σ.read .rsp) 8 = some v) :
    Silmaril.X86.popWord σ mem = some (v, σ.write .rsp (σ.read .rsp + 8#64)) := by
  simp only [Silmaril.X86.Ext.loadN, Option.map_eq_some_iff] at h
  obtain ⟨bytes, hr, rfl⟩ := h
  have hl := Silmaril.Process.Memory.readWith_length hr
  match bytes, hl with
  | [b0, b1, b2, b3, b4, b5, b6, b7], _ =>
    simp [Silmaril.X86.popWord, hr, wordOfBytes?_eq]

theorem pushWord_storeN (σ : State) (mem : Silmaril.Process.Memory) (v : Word) :
    Silmaril.X86.pushWord σ mem v =
      (Silmaril.X86.Ext.storeN mem (σ.read .rsp - 8#64) 8 v).map
        fun m' => (σ.write .rsp (σ.read .rsp - 8#64), m') := by
  simp [Silmaril.X86.pushWord, Silmaril.X86.Ext.storeN, Silmaril.X86.Ext.leBytes_eight]

end Silmaril.Sim.X86.GM
