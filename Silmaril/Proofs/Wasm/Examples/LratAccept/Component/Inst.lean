module

public import Silmaril.Wasm.Examples.LratAccept.Component.Defs
public import Silmaril.Wasm.Examples.LratAccept.Thms
public import Silmaril.Wasm.Component.Reference.ListLift.Bump.Defs
public import Silmaril.Wasm.Verify.Check.Thms
public import Silmaril.Wasm.Component.Reference.Engine.Core3.Store.Defs

/-!
# The LRAT acceptor component: the instance and the allocator

`accI` is the instance of `prog` (`instOf`, `IsInstance` by `isInstance_instOf`); its facts are
kernel evaluations (`t_*`): the function exports `cabi_realloc`, `check-stream`,
`check-nested` at the addresses `10`, `11`, `12`, of type `[i32 i32 i32 i32] → [i32]`; the
memory export `memory` is the module's memory `1`, a 32-bit memory; the instance store is a
store of the acceptor (`AccStore`) with the heap pointer at `heapBase`.

* `lratComp_good`, `lratComp_inst`: `lratComp` is in the fragment of `acceptSound`;
* `lratBump`: `cabi_realloc` (address `10`) is a bump allocator (`BumpAlloc`) for memory
  address `1` and the invariant `LInvL`: a store of the acceptor with heap pointer
  `t ≤ memBytes`. From `realloc_sound`: the allocator only sets the heap pointer, the block lies
  above the old heap pointer and ends below the new one, or it is `memBytes` (then only an empty
  block passes the bounds check). Writes to memory `1` keep `AccStore` (with the new ABI
  memory); the LRAT state (memory `0`, globals `0 … 7`) is untouched by the lowering.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Examples.LratAccept.Component

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation Silmaril.Wasm.Game Silmaril.Wasm.Verify
open Silmaril.Wasm.Examples.LratAccept
open Silmaril.Wasm.Component.Reference.ListLift
open Silmaril.Wasm.Numerics (Profile)

set_option maxRecDepth 100000

theorem t_instance : (instance? prog).isSome = true := by decide +kernel

theorem t_imports : accI.imports = [] := by decide +kernel

theorem t_memType : Silmaril.Wasm.SingleThreaded.memAddrType? accI.store 1 = some .i32 := by
  decide +kernel

theorem t_memAddr : 1 < accI.store.mems.length := by decide +kernel

theorem t_coreAddrs : lratComp.coreAddr accI "cabi_realloc" = 10 ∧
    lratComp.coreAddr accI "check-stream" = 11 ∧ lratComp.coreAddr accI "check-nested" = 12 := by
  decide +kernel

/-- The initial values of the eight LRAT globals. -/
def gInit : List (BitVec 32) := [0, 24576, 24576, 0, 0, 0, 0, 1]

theorem t_accS_globals : accS.globals = (gInit ++ [16]).map fun v => ⟨accGt, Val.i32 v⟩ := by
  decide +kernel

theorem t_accS_types : accS.mems.map (·.type) = [lratMemType, accMt] := by decide +kernel

theorem t_accS_sizes : accS.mems.map (·.bytes.size) =
    [Silmaril.Wasm.Examples.LRAT.memSize, memBytes] := by
  decide +kernel

theorem t_exports : accI.exports = [reallocFnType, reallocFnType, reallocFnType] := by
  decide +kernel

theorem gInit_length : gInit.length = 8 := rfl

/-- The two memories of the instance store. -/
theorem accS_mems : ∃ B₀ B₁, accS.mems = [⟨lratMemType, B₀⟩, ⟨accMt, B₁⟩] ∧
    B₀.size = Silmaril.Wasm.Examples.LRAT.memSize ∧ B₁.size = memBytes := by
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

theorem lratComp_good : lratComp.Good :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem lratComp_inst : lratComp.Inst accI where
  inst := by
    have h := isInstance_instOf t_instance
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
    simp only [lratComp, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ⟨1, by rw [t_exports]; decide, by rw [exportAddrs]; exact t_coreAddrs.2.1.symm,
        by simp only [t_exports]; rfl⟩
    · exact ⟨2, by rw [t_exports]; decide, by rw [exportAddrs]; exact t_coreAddrs.2.2.symm,
        by simp only [t_exports]; rfl⟩

/-! ## The allocator -/

theorem toNat_ofNat {q : Nat} (h : q < 2 ^ 32) : (BitVec.ofNat 32 q).toNat = q := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- The instance store is a store of the acceptor, with the heap pointer at `heapBase`. -/
theorem lInvL_init : LInvL accI.store heapBase := by
  obtain ⟨B₀, B₁, hm, h₀, h₁⟩ := accS_mems
  have e : accI.store = accS := by unfold accS; rfl
  rw [e]
  refine ⟨⟨gInit, B₀, B₁, ⟨rfl, ?_, gInit_length, hm, h₀, h₁⟩⟩, by decide⟩
  show accS.globals = _
  rw [t_accS_globals, List.map_append]
  rfl

theorem modify_append_singleton {α : Type} (l : List α) (x : α) (f : α → α) :
    (l ++ [x]).modify l.length f = l ++ [f x] := by
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_modify]
  split
  · next h =>
    subst h
    simp
  · next h =>
    rcases Nat.lt_or_ge j l.length with hj | hj
    · simp [List.getElem?_append_left hj]
    · have hj' : l.length < j := Nat.lt_of_le_of_ne hj h
      rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
      rfl

theorem globals_8 {G : List (BitVec 32)} (hG : G.length = 8) (top : BitVec 32) :
    ((G.map fun v => (⟨accGt, Val.i32 v⟩ : GlobalInst)) ++ [⟨accGt, Val.i32 top⟩])[8]? =
      some ⟨accGt, Val.i32 top⟩ := by
  rw [List.getElem?_append_right (by simp [hG])]
  simp [hG]

theorem globals_set8 {G : List (BitVec 32)} (hG : G.length = 8) (top v : BitVec 32) :
    ((G.map fun v => (⟨accGt, Val.i32 v⟩ : GlobalInst)) ++
        [(⟨accGt, Val.i32 top⟩ : GlobalInst)]).modify 8
        (fun g : GlobalInst => { g with value := Val.i32 v }) =
      (G.map fun v => (⟨accGt, Val.i32 v⟩ : GlobalInst)) ++ [⟨accGt, Val.i32 v⟩] := by
  have hl : (G.map fun v => (⟨accGt, Val.i32 v⟩ : GlobalInst)).length = 8 := by simp [hG]
  rw [← hl, modify_append_singleton]

/-- **`cabi_realloc` is a bump allocator** (function address `10`, memory address `1`). -/
theorem lratBump (P : Profile) : BumpAlloc P 10 1 memBytes LInvL where
  small := by decide
  size := by
    rintro s t ⟨⟨G, B₀, B₁, h⟩, -⟩
    simp [memBytesOf, h.mems, h.size₁]
  write := by
    rintro s t p bs s' ⟨⟨G, B₀, B₁, h⟩, ht⟩ hw
    obtain ⟨mi, b, hm', hwb, rfl⟩ := Silmaril.Wasm.Component.Engine.Core3.memWrite?_eq_some hw
    rw [h.mems] at hm'
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hm'
    subst hm'
    refine ⟨⟨G, B₀, b, ⟨h.funcs, h.globals, h.len, ?_, h.size₀, ?_⟩⟩, ht⟩
    · show s.mems.set 1 _ = _
      rw [h.mems]
      rfl
    · rw [Memory.writeBytes_size _ _ _ _ hwb, h.size₁]
  realloc := by
    rintro s t al n q s' ⟨⟨G, B₀, B₁, h⟩, ht⟩ ⟨f', hs, hq⟩
    have hmb : memBytes = 1048576 := rfl
    have htn : (BitVec.ofNat 32 t).toNat = t := toNat_ofNat (by omega)
    have hg : s.globals[8]? = some ⟨accGt, Val.i32 (BitVec.ofNat 32 t)⟩ := by
      rw [h.globals]
      exact globals_8 h.len _
    obtain ⟨r, t', hres, rfl, hok⟩ :=
      realloc_sound h.funcs hg (by rw [htn]; exact ht) hs
    simp only [List.cons.injEq, and_true] at hres
    have hr : BitVec.ofNat 32 q = r := by
      injection hres with h₁
      injection h₁
    have hqr : q = r.toNat := by rw [← hr, toNat_ofNat hq]
    obtain ⟨hlo, hhi, hcase⟩ := hok
    rw [htn] at hlo hcase
    refine ⟨t'.toNat, ⟨⟨G, B₀, B₁, ⟨h.funcs, ?_, h.len, h.mems, h.size₀, h.size₁⟩⟩, hhi⟩, ?_,
      ?_, ?_⟩
    · show s.globals.modify 8 _ = _
      rw [h.globals, globals_set8 h.len, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rfl
    · rcases hcase with ⟨-, h₁, -⟩ | ⟨h₁, -⟩ <;> omega
    · intro hb
      have hn : (BitVec.ofNat 32 n).toNat = n := toNat_ofNat (by omega)
      rw [hn] at hcase
      rcases hcase with ⟨-, -, h₁⟩ | ⟨h₁, h₂⟩ <;> omega

end Silmaril.Proofs.Wasm.Examples.LratAccept.Component
