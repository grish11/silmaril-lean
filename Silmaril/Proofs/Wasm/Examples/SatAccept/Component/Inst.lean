module

public import Silmaril.Wasm.Examples.SatAccept.Component.Defs
public import Silmaril.Wasm.Examples.SatAccept.Thms
public import Silmaril.Wasm.Component.Reference.ListLift.Bump.Defs
public import Silmaril.Wasm.Verify.Check.Thms
public import Silmaril.Wasm.Logic.VC.Thms
public import Silmaril.Wasm.Component.Reference.Engine.Core3.Store.Defs

/-!
# The SAT acceptor component: the instance and the allocator

`satI` is the instance of `prog` (`instOf`, `IsInstance` by `isInstance_instOf`); its facts are
kernel evaluations (`t_*`): three functions with the code of `prog`, of type
`[i32 i32 i32 i32] → [i32]`, whose module instance has memory address `0` and global address
`0` (the heap pointer, initially `heapBase`); one memory of `memBytes` bytes, 32-bit.

* `satComp_good`, `satComp_inst`: `satComp` is in the fragment of `acceptSound`;
* `satBump`: `cabi_realloc` is a bump allocator (`BumpAlloc`) for the invariant `SInv`: the
  functions of `satI`, one memory of `memBytes` bytes and the heap pointer `t ≤ memBytes`. From
  `realloc_returns`: the block lies above the heap pointer and ends below the new one, or it is
  `memBytes` (then only an empty block passes the bounds check).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Examples.SatAccept.Component

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation Silmaril.Wasm.Game Silmaril.Wasm.Verify
open Silmaril.Wasm.Examples.SatAccept
open Silmaril.Wasm.Component.Reference.ListLift
open Silmaril.Wasm.Logic.VC (globalVal setGlobalIdx)
open Silmaril.Wasm.Numerics (Profile)

/-- The type of the three functions. -/
abbrev ty4 : CCompType := fnType4.toComp

set_option maxRecDepth 100000

theorem t_instance : (instance? prog).isSome = true := by decide +kernel

theorem t_shape : satI.imports = [] ∧ satI.exports = [fnType4, fnType4, fnType4] ∧
    satI.addrs = [0, 1, 2] := by
  decide +kernel

theorem t_nfuncs : satI.store.funcs.length = 3 := by decide +kernel

theorem t_code : satI.store.funcs.map FuncInst.code =
    [.wasm prog.funcs[0], .wasm prog.funcs[1], .wasm prog.funcs[2]] := rfl

theorem t_types : satI.store.funcs.map (·.type.expand?) = [some ty4, some ty4, some ty4] := by
  decide +kernel

theorem t_mods : satI.store.funcs.map (fun fi => (fi.module.mems, fi.module.globals)) =
    [([0], [0]), ([0], [0]), ([0], [0])] := by
  decide +kernel

theorem t_mems : satI.store.mems.map (·.bytes.size) = [memBytes] := by decide +kernel

theorem t_memType : Silmaril.Wasm.SingleThreaded.memAddrType? satI.store 0 = some .i32 := by
  decide +kernel

theorem t_global : globalVal satI.store satM 0 = some (.i32 (BitVec.ofNat 32 heapBase)) := by
  decide +kernel

theorem t_coreAddrs : satComp.coreAddr satI "cabi_realloc" = 0 ∧
    satComp.coreAddr satI "check-stream" = 1 ∧ satComp.coreAddr satI "check-nested" = 2 := by
  decide +kernel

/-- The three functions of the instance. -/
theorem funcs_eq : ∃ f₀ f₁ f₂ : FuncInst Nat, satI.store.funcs = [f₀, f₁, f₂] ∧
    f₀.code = .wasm prog.funcs[0] ∧ f₁.code = .wasm prog.funcs[1] ∧
    f₂.code = .wasm prog.funcs[2] ∧
    Expand f₀.type ty4 ∧ Expand f₁.type ty4 ∧ Expand f₂.type ty4 ∧
    f₀.module.mems = [0] ∧ f₁.module.mems = [0] ∧ f₂.module.mems = [0] ∧
    f₀.module.globals = [0] ∧ f₁.module.globals = [0] ∧ f₂.module.globals = [0] := by
  obtain ⟨f₀, f₁, f₂, h⟩ := List.length_eq_three.1 t_nfuncs
  have hc := t_code
  have ht := t_types
  have hm := t_mods
  rw [h] at hc ht hm
  simp only [List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq, and_true] at hc ht hm
  exact ⟨f₀, f₁, f₂, h, hc.1, hc.2.1, hc.2.2, Expand.iff.2 ht.1, Expand.iff.2 ht.2.1,
    Expand.iff.2 ht.2.2, hm.1.1, hm.2.1.1, hm.2.2.1, hm.1.2, hm.2.1.2, hm.2.2.2⟩

theorem satM_eq {f₀ f₁ f₂ : FuncInst Nat} (h : satI.store.funcs = [f₀, f₁, f₂]) :
    satM = f₀.module := by
  simp [satM, h]

theorem globalVal_congr {s : Store Nat} {m m' : ModuleInst} (h : m.globals = m'.globals)
    (x : Nat) : globalVal s m x = globalVal s m' x := by
  unfold globalVal
  rw [h]

theorem ty4_params : (Ty.ofList (fnType4.params.map ScalarType.toC)).length = 4 := rfl

theorem ty4_results : (Ty.ofList (fnType4.results.map ScalarType.toC)).length = 1 := rfl

/-! ## The fragment -/

theorem satComp_good : satComp.Good := ⟨by decide +kernel, by decide +kernel⟩

theorem satComp_inst : satComp.Inst satI where
  inst := isInstance_instOf t_instance
  noImports := t_shape.1
  memExport := by decide +kernel
  memAddr := by decide +kernel
  reallocFunc := by decide +kernel
  coreFuncs := by decide +kernel
  memI32 := t_memType
  realloc := ⟨0, by decide +kernel, by decide +kernel, by decide +kernel⟩
  core := by
    intro x hx
    simp only [satComp, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ⟨1, by decide +kernel, by decide +kernel, by decide +kernel⟩
    · exact ⟨2, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-! ## The allocator -/

theorem sInv_init : SInv satI.store heapBase := by
  refine ⟨rfl, ?_, t_global, by decide⟩
  have h := t_mems
  obtain ⟨m, hm⟩ : ∃ m, satI.store.mems = [m] := by
    cases e : satI.store.mems with
    | nil => rw [e] at h; cases h
    | cons m l =>
      rw [e] at h
      cases l with
      | nil => exact ⟨m, rfl⟩
      | cons _ _ => simp at h
  rw [hm] at h
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
  exact ⟨m.type, m.bytes, by rw [hm]; rfl, h⟩

theorem i32_inj {a b : BitVec 32} (h : Val.i32 a = Val.i32 b) : a = b := by
  injection h with h₁
  injection h₁

/-- **`cabi_realloc` is a bump allocator.** -/
theorem satBump (P : Profile) : BumpAlloc P 0 0 memBytes SInv where
  small := by decide
  size := by
    rintro s t ⟨_, ⟨mt, B, hm, hB⟩, _⟩
    simp [memBytesOf, hm, hB]
  write := by
    rintro s t p bs s' ⟨hf, ⟨mt, B, hm, hB⟩, hg, ht⟩ hw
    obtain ⟨mi, b, hm', hwb, rfl⟩ := Silmaril.Wasm.Component.Engine.Core3.memWrite?_eq_some hw
    rw [hm] at hm'
    cases hm'
    have hlt : 0 < s.mems.length := (List.getElem?_eq_some_iff.mp hm).1
    refine ⟨hf, ⟨mt, b, ?_, ?_⟩, hg, ht⟩
    · simp [Store.setMem, List.getElem?_set_self hlt]
    · rw [Memory.writeBytes_size _ _ _ _ hwb, hB]
  realloc := by
    rintro s t n q s' ⟨hf, hmem, hg, ht⟩ ⟨f', hs, hq⟩
    obtain ⟨f₀, f₁, f₂, hF, hc₀, -, -, he₀, -, -, -, -, -, -, -, -⟩ := funcs_eq
    have hfi : s.funcs[0]? = some f₀ := by rw [hf, hF]; rfl
    have hg' : globalVal s f₀.module 0 = some (.i32 (BitVec.ofNat 32 t)) := satM_eq hF ▸ hg
    obtain ⟨hres, rfl, hok⟩ := realloc_returns hfi hc₀ he₀ ty4_params ty4_results hg' hs
    simp only [List.cons.injEq, and_true] at hres
    have hr := i32_inj hres
    set r := reallocRes (BitVec.ofNat 32 t) (BitVec.ofNat 32 4) (BitVec.ofNat 32 n)
    have hqr : q = r.1.toNat := by
      rw [← hr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq]
    have hmb : memBytes = 1048576 := rfl
    have htn : (BitVec.ofNat 32 t).toNat = t := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    refine ⟨r.2.toNat, ⟨by simp [Silmaril.Wasm.Logic.VC.setGlobalIdx_funcs, hf], ?_, ?_, ?_⟩,
      ?_, ?_, ?_⟩
    · simpa [Silmaril.Wasm.Logic.VC.setGlobalIdx_mems] using hmem
    · rw [globalVal_congr (congrArg ModuleInst.globals (satM_eq hF)) 0, Silmaril.Wasm.Logic.VC.globalVal_setGlobalIdx_self, hg']
      simp
    · unfold ReallocOk at hok
      omega
    · simp [memBytesOf, Silmaril.Wasm.Logic.VC.setGlobalIdx_mems]
    · unfold ReallocOk at hok
      omega
    · intro hb
      have hn : (BitVec.ofNat 32 n).toNat = n := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      unfold ReallocOk at hok
      omega

end Silmaril.Proofs.Wasm.Examples.SatAccept.Component
