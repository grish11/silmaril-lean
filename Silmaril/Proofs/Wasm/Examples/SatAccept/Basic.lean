module

public import Silmaril.Wasm.Examples.SatAccept.Defs
public import Silmaril.Wasm.Verify.FnSpec.Thms
public import Silmaril.Wasm.Logic.Words.Thms

/-!
# The SAT acceptor: the verification-condition tactic and `cabi_realloc`

* `sat_simp`: the `wat_vc` evaluation of `Silmaril.Wasm.Logic.VC.wpc` (the lemmas of
  `wat_vc_simp`) keeping `bool32` folded, so that the checks' Boolean locals stay `bool32 b`,
  and keeping addresses as `(p + i <<< 2).toNat` (resolved by `addr4` once the loop bounds are
  in context);
* the binder lemmas `forall_store_eq`, `forall_params_nil`, `forall_frame_module`,
  `forall_locals_swap` with which `simp` eliminates the store, the loop parameters and the frame
  that a loop's condition quantifies over, for invariants fixing them;
* `realloc_vc`: `cabi_realloc` meets `reallocSpec`; `reallocRes_ok`: its result is a block
  above the old heap pointer within memory, or `memBytes`.

New proofs, following `Silmaril.Proofs.Wasm.Examples.MemberCheck`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Examples.SatAccept

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Verify Silmaril.Wasm.Logic.Words
open Silmaril.Wasm.Examples.SatAccept
open Silmaril.Wasm.Logic.VC (globalVal setGlobalIdx)

/-- The generator's simp lemmas (`wat_vc_simp` without unfolding `bool32`). -/
syntax "sat_simp" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| sat_simp) => `(tactic| sat_simp [])
  | `(tactic| sat_simp [$ls,*]) => `(tactic|
      simp (maxSteps := 100000000) [Silmaril.Wasm.Logic.VC.wpc, Silmaril.Wasm.Logic.VC.ctl,
        Silmaril.Wasm.Logic.VC.loops, Silmaril.Wasm.Logic.VC.enterVC,
        Silmaril.Wasm.Logic.VC.labelQ, Silmaril.Wasm.Logic.VC.loopQ,
        Silmaril.Wasm.Logic.VC.popI32, Silmaril.Wasm.Logic.VC.popSelect,
        Silmaril.Wasm.Execution.Core.Frame.forCall, Silmaril.Wasm.Examples.Common.bodyPost,
        Silmaril.Wasm.Execution.Core.ModuleInst.blockType?, Silmaril.Wasm.Logic.VC.defaultVal_i32,
        Silmaril.Wasm.Logic.VC.vc_exec1_nop, Silmaril.Wasm.Logic.VC.vc_exec1_drop,
        Silmaril.Wasm.Logic.VC.vc_exec1_intConst, Silmaril.Wasm.Logic.VC.vc_exec1_i32Const,
        Silmaril.Wasm.Logic.VC.vc_exec1_localGet, Silmaril.Wasm.Logic.VC.vc_exec1_localSet,
        Silmaril.Wasm.Logic.VC.vc_exec1_localTee, Silmaril.Wasm.Logic.VC.vc_exec1_intUnOp,
        Silmaril.Wasm.Logic.VC.vc_exec1_intBinOp, Silmaril.Wasm.Logic.VC.vc_exec1_intTestOp,
        Silmaril.Wasm.Logic.VC.vc_exec1_intRelOp, Silmaril.Wasm.Logic.VC.vc_exec1_intLoad,
        Silmaril.Wasm.Logic.VC.exec1_globalGet_idx, Silmaril.Wasm.Logic.VC.exec1_globalSet_if,
        Silmaril.Wasm.Logic.VC.globalVal_setGlobalIdx_self,
        Silmaril.Wasm.Logic.Core.popInt, Silmaril.Wasm.Logic.Core.popV,
        Silmaril.Wasm.Logic.Core.localVal?, Silmaril.Wasm.Execution.Core.Frame.local?,
        Silmaril.Wasm.Execution.Core.Frame.setLocal, Silmaril.Wasm.Idx.toNat,
        Silmaril.Wasm.Execution.Core.Val.i32, Silmaril.Wasm.Logic.VC.numVal_i32_eq,
        Silmaril.Wasm.Logic.VC.and_ones32, Silmaril.Wasm.Logic.VC.intTestOp_i32,
        Silmaril.Wasm.Logic.Core.ofNat_i32_width, Silmaril.Wasm.Logic.Core.setWidth_i32_width,
        -Silmaril.Wasm.Logic.Core.intTestOp_eqz, Silmaril.Wasm.Logic.Core.bool32_and,
        Silmaril.Wasm.Execution.Core.Store.mem?, Silmaril.Wasm.Execution.Core.effAddr,
        Silmaril.Wasm.IntType.width, Silmaril.Wasm.Verify.load_ite, -BitVec.toNat_add,
        -BitVec.toNat_shiftLeft, $ls,*])

/-! Binder normalisation for loop invariants that fix the store, the loop parameters and the
frame: `simp` eliminates the quantified store and frame of a loop's condition with these. -/

theorem forall_store_eq {P : Store Nat → Frame → List Val → Prop} {s₀ : Store Nat} :
    (∀ s f a, s = s₀ → P s f a) ↔ ∀ f a, P s₀ f a :=
  ⟨fun h f a => h s₀ f a rfl, fun h _ f a hs => hs ▸ h f a⟩

theorem forall_store_eq₂ {P : Store Nat → Frame → Prop} {s₀ : Store Nat} :
    (∀ s f, s = s₀ → P s f) ↔ ∀ f, P s₀ f :=
  ⟨fun h f => h s₀ f rfl, fun h _ f hs => hs ▸ h f⟩

theorem forall_params_nil {P : Frame → List Val → Prop} :
    (∀ f (a : List Val), a = [] → P f a) ↔ ∀ f, P f [] :=
  ⟨fun h f => h f [] rfl, fun h f _ ha => ha ▸ h f⟩

theorem forall_frame_module {P : Frame → Prop} {mi : ModuleInst} :
    (∀ f : Frame, f.module = mi → P f) ↔ ∀ ls, P ⟨ls, mi⟩ :=
  ⟨fun h ls => h ⟨ls, mi⟩ rfl, fun h f hf => by obtain ⟨ls, m⟩ := f; cases hf; exact h ls⟩

theorem forall_locals_swap {P : List (Option Val) → BitVec 32 → Prop} :
    (∀ ls (x : BitVec 32), P ls x) ↔ ∀ x ls, P ls x :=
  ⟨fun h x ls => h ls x, fun h ls x => h x ls⟩

theorem forall_memAt {P : Nat → MemoryType → ByteArray → Prop} {s : Store Nat} {ma : Nat}
    {mt : MemoryType} {B : ByteArray} (hm : s.mems[ma]? = some ⟨mt, B⟩) :
    (∀ ma' mt' B', ma = ma' → s.mems[ma']? = some ⟨mt', B'⟩ → P ma' mt' B') ↔ P ma mt B := by
  constructor
  · intro h; exact h ma mt B rfl hm
  · rintro h ma' mt' B' rfl h'
    rw [hm] at h'
    cases h'
    exact h

/-- The address of word `i` of an array at `p` in memory (`p + (i << 2)`, no wrapping). -/
theorem addr4 {p i : BitVec 32} {n : Nat} (hi : i.toNat < n) (hb : p.toNat + 4 * n ≤ memBytes) :
    (p + i <<< 2).toNat = p.toNat + 4 * i.toNat := by
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  simp only [memBytes] at hb
  have : i.toNat * 2 ^ 2 % 2 ^ 32 = 4 * i.toNat := Nat.mod_eq_of_lt (by omega) |>.trans (by ring)
  omega

theorem succ_toNat {x y : BitVec 32} (h : x.toNat < y.toNat) : (x + 1#32).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add]
  have := y.isLt
  simp only [BitVec.toNat_ofNat]
  omega

theorem pred_toNat {x : BitVec 32} (h : x ≠ 0#32) : (x - 1#32).toNat = x.toNat - 1 := by
  have : x.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
  rw [BitVec.toNat_sub]
  have := x.isLt
  simp only [BitVec.toNat_ofNat]
  omega

theorem bool32_true : Silmaril.Wasm.Numerics.bool32 true = 1#32 := rfl
theorem bool32_false : Silmaril.Wasm.Numerics.bool32 false = 0#32 := rfl
theorem intMin_eq : BitVec.intMin 32 = 2147483648#32 := by decide
theorem litWord_eq (x : BitVec 32) :
    Silmaril.Logic.SAT.Carrier.LitWord x = (x != 0#32 && x != 2147483648#32) := by
  simp [Silmaril.Logic.SAT.Carrier.LitWord, intMin_eq]

theorem bool32_ite (b : Bool) : Silmaril.Wasm.Numerics.bool32 b = if b = true then 1#32 else 0#32 := by
  cases b <;> rfl

theorem alignUp_eq (t al : BitVec 32) : (t + (al - 1#32) &&& -al) = alignUp t al := by
  simp [alignUp]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem realloc_vc : reallocSpec.vc prog.funcs[0] := by
  simp only [Silmaril.Wasm.Verify.FnSpec.vc, reallocSpec, prog]
  intro x mi s hpre
  obtain ⟨o, os, al, n, t⟩ := x
  sat_simp [hpre, alignUp_eq, BitVec.toNat_add]
  have hp := (alignUp t al).isLt
  constructor
  · intro h1 h2 h3
    have h4 : (alignUp t al).toNat + n.toNat ≤ memBytes := by simp only [memBytes]; omega
    simp [reallocRes, h1, h4]
  · intro h
    have h4 : ¬ (t.toNat ≤ (alignUp t al).toNat ∧ (alignUp t al).toNat + n.toNat ≤ memBytes) := by
      simp only [memBytes]; omega
    simp [reallocRes, h4]

/-- **The non-overlap property** of `reallocRes`. -/
theorem reallocRes_ok (t al n : BitVec 32) :
    ReallocOk t n (reallocRes t al n).1 (reallocRes t al n).2 := by
  unfold reallocRes ReallocOk
  split
  · rename_i h
    dsimp only
    refine Or.inl ⟨h.1, h.2, ?_⟩
    simp only [memBytes] at h
    rw [BitVec.toNat_add]
    omega
  · exact Or.inr ⟨by simp [memBytes], by simp [memBytes]⟩

end Silmaril.Proofs.Wasm.Examples.SatAccept
