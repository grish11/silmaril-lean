module

public import Silmaril.Wasm.Examples.FarkasAccept.Component.Defs
public import Silmaril.Wasm.Examples.FarkasAccept.Thms
public import Silmaril.Wasm.Component.Reference.ListLift.Bump.Defs
public import Silmaril.Wasm.Verify.Check.Thms
public import Silmaril.Wasm.Component.Reference.Engine.Core3.Store.Defs

/-!
# The Farkas acceptor component: the instance and the allocator

`accI` is the instance of `prog` (`instOf`, `IsInstance` by `isInstance_instOf`); its facts are
kernel evaluations (`t_*`): the function exports `cabi_realloc`, `check` at the addresses `3`,
`4`, of type `[i32 i32 i32 i32] → [i32]`; the memory export `memory` is the module's memory `1`,
a 32-bit memory; the instance store is a store of the acceptor (`AccStore`) with the heap
pointer at `heapBase`.

* `farkasComp_good`, `farkasComp_inst`: `farkasComp` is in the fragment of `acceptSound`;
* `farkasBump`: `cabi_realloc` (address `3`) is a bump allocator (`BumpAlloc`) for memory
  address `1` and the invariant `FInv`: a store of the acceptor with heap pointer
  `t ≤ memBytes`. From `realloc_sound`: at every alignment the allocator only sets the heap
  pointer, the block lies above the old heap pointer and ends below the new one, or it is
  `memBytes` (then only an empty block passes the bounds check). Writes to memory `1` keep
  `AccStore` (with the new ABI memory); the checker state (memory `0`, globals `0 … 3`) is
  untouched by the lowering.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Examples.FarkasAccept.Component

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation Silmaril.Wasm.Game Silmaril.Wasm.Verify
open Silmaril.Wasm.Examples.FarkasAccept
open Silmaril.Wasm.Component.Reference.ListLift
open Silmaril.Wasm.Numerics (Profile)

set_option maxRecDepth 100000

theorem t_imports : accI.imports = [] := by decide +kernel

theorem t_memType : Silmaril.Wasm.SingleThreaded.memAddrType? accI.store 1 = some .i32 := by
  decide +kernel

theorem t_memAddr : 1 < accI.store.mems.length := by decide +kernel

theorem t_coreAddrs : farkasComp.coreAddr accI "cabi_realloc" = 3 ∧
    farkasComp.coreAddr accI "check" = 4 := by
  decide +kernel

theorem t_accS_globals : accS.globals = [⟨accG32, Val.i32 0⟩, ⟨accG32, Val.i32 0⟩,
    ⟨accG64, Val.i64 0⟩, ⟨accG64, Val.i64 0⟩, ⟨accG32, Val.i32 (BitVec.ofNat 32 heapBase)⟩] := by
  decide +kernel

theorem t_accS_types : accS.mems.map (·.type) = [farkasMemType, accMt] := by decide +kernel

theorem t_accS_sizes : accS.mems.map (·.bytes.size) = [65536, memBytes] := by decide +kernel

theorem t_exports : accI.exports = [reallocFnType, reallocFnType] := by decide +kernel

/-- The two memories of the instance store. -/
theorem accS_mems : ∃ B₀ B₁, accS.mems = [⟨farkasMemType, B₀⟩, ⟨accMt, B₁⟩] ∧
    B₀.size = 65536 ∧ B₁.size = memBytes := by
  have ht := t_accS_types
  have hs := t_accS_sizes
  match e : accS.mems with
  | [m₀, m₁] =>
    rw [e] at ht hs
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at ht hs
    obtain ⟨t₀, b₀⟩ := m₀
    obtain ⟨t₁, b₁⟩ := m₁
    simp only at ht hs
    obtain ⟨rfl, rfl⟩ := ht
    exact ⟨b₀, b₁, rfl, hs.1, hs.2⟩
  | [] => rw [e] at ht; cases ht
  | [_] => rw [e] at ht; simp at ht
  | _ :: _ :: _ :: _ => rw [e] at ht; simp at ht

/-! ## The fragment -/

theorem farkasComp_good : farkasComp.Good :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem farkasComp_inst : farkasComp.Inst accI where
  inst := by
    have h := isInstance_instOf instance_isSome
    unfold accI
    exact h
  noImports := t_imports
  memExport := ⟨⟨"memory", .memory ⟨1⟩⟩, List.mem_cons_self, rfl, ⟨1⟩, rfl, rfl⟩
  memAddr := t_memAddr
  reallocFunc := by decide +kernel
  coreFuncs := by decide +kernel
  memI32 := t_memType
  realloc := ⟨0, by rw [t_exports]; decide, by rw [exportAddrs]; exact t_coreAddrs.1.symm,
    by simp only [t_exports]; rfl⟩
  core := by
    intro x hx
    simp only [farkasComp, List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx
    exact ⟨1, by rw [t_exports]; decide, by rw [exportAddrs]; exact t_coreAddrs.2.symm,
      by simp only [t_exports]; rfl⟩

/-! ## The allocator -/

theorem toNat_ofNat {q : Nat} (h : q < 2 ^ 32) : (BitVec.ofNat 32 q).toNat = q := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- The instance store is a store of the acceptor, with the heap pointer at `heapBase`. -/
theorem fInv_init : FInv accI.store heapBase := by
  obtain ⟨B₀, B₁, hm, h₀, h₁⟩ := accS_mems
  have e : accI.store = accS := by unfold accS; rfl
  rw [e]
  exact ⟨⟨B₁, ⟨rfl, ⟨0, 0, 0, 0, t_accS_globals⟩, ⟨B₀, h₀, hm⟩, h₁⟩⟩, by decide⟩

/-- **`cabi_realloc` is a bump allocator** (function address `3`, memory address `1`). -/
theorem farkasBump (P : Profile) : BumpAlloc P 3 1 memBytes FInv where
  small := by decide
  size := by
    rintro s t ⟨⟨B₁, h⟩, -⟩
    obtain ⟨B₀, -, hm⟩ := h.mems
    simp [memBytesOf, hm, h.size₁]
  write := by
    rintro s t p bs s' ⟨⟨B₁, h⟩, ht⟩ hw
    obtain ⟨B₀, h₀, hm⟩ := h.mems
    obtain ⟨mi, b, hm', hwb, rfl⟩ := Silmaril.Wasm.Component.Engine.Core3.memWrite?_eq_some hw
    rw [hm] at hm'
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hm'
    subst hm'
    refine ⟨⟨b, ⟨h.funcs, h.globals, ⟨B₀, h₀, ?_⟩, ?_⟩⟩, ht⟩
    · show s.mems.set 1 _ = _
      rw [hm]
      rfl
    · rw [Memory.writeBytes_size _ _ _ _ hwb, h.size₁]
  realloc := by
    rintro s t al n q s' ⟨⟨B₁, h⟩, ht⟩ ⟨f', hs, hq⟩
    have hmb : memBytes = 1048576 := rfl
    have htn : (BitVec.ofNat 32 t).toNat = t := toNat_ofNat (by omega)
    obtain ⟨bad, hr₀, y, vb, hgl⟩ := h.globals
    have hg : s.globals[4]? = some ⟨accG32, Val.i32 (BitVec.ofNat 32 t)⟩ := by
      rw [hgl]
      rfl
    obtain ⟨r, t', hres, rfl, hok⟩ := realloc_sound h.funcs hg (by rw [htn]; exact ht) hs
    simp only [List.cons.injEq, and_true] at hres
    have hr : BitVec.ofNat 32 q = r := by
      injection hres with h₁
      injection h₁
    have hqr : q = r.toNat := by rw [← hr, toNat_ofNat hq]
    obtain ⟨hlo, hhi, hcase⟩ := hok
    rw [htn] at hlo hcase
    refine ⟨t'.toNat, ⟨⟨B₁, ⟨h.funcs, ⟨bad, hr₀, y, vb, ?_⟩, h.mems, h.size₁⟩⟩, hhi⟩, ?_, ?_, ?_⟩
    · show s.globals.modify 4 _ = _
      rw [hgl, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      rfl
    · rfl
    · rcases hcase with ⟨-, h₁, -⟩ | ⟨h₁, -⟩ <;> omega
    · intro hb
      have hn : (BitVec.ofNat 32 n).toNat = n := toNat_ofNat (by omega)
      rw [hn] at hcase
      rcases hcase with ⟨-, -, h₁⟩ | ⟨h₁, h₂⟩ <;> omega

end Silmaril.Proofs.Wasm.Examples.FarkasAccept.Component
