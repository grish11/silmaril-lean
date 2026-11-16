module

public import Silmaril.Sim.X86.Max2.Defs
public import Silmaril.Wasm.Logic.VCTotal.Thms
public import Silmaril.X86.Ext.Flags

/-!
# The `max2` problem: the state invariant under updates

`Good` (`Silmaril.Sim.X86.Max2.Defs`) is preserved by writing an `i64` register global, an `i32`
flag global, or memory `ma` (same size); `R`/`Fl` read back what was written and are unchanged
elsewhere (the frame rule `globalVal_setGlobalIdx_ne`); `memB` reads memory `ma`.
-/

@[expose] public section

namespace Silmaril.Sim.X86.Max2

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Logic.VC

variable {H : Type} {mi : ModuleInst} {ma : Nat} {mt : MemoryType} {fis : Nat → FuncInst H}
  {s : Store H} {x k : Nat}

theorem globalVal_R (h : Good mi ma mt fis s) (hk : k < 17) :
    globalVal s mi k = some (.num ⟨.int .i64, R s mi k⟩) := by
  obtain ⟨v, hv⟩ := h.regs k hk
  simp [R, hv]

theorem globalVal_Fl (h : Good mi ma mt fis s) (hk : 17 ≤ k) (hk' : k < 24) :
    globalVal s mi k = some (.num ⟨.int .i32, Fl s mi k⟩) := by
  obtain ⟨v, hv⟩ := h.flags k hk hk'
  simp [Fl, hv]

theorem good_isSome (h : Good mi ma mt fis s) (hx : x < 24) : (globalVal s mi x).isSome := by
  by_cases h17 : x < 17
  · rw [globalVal_R h h17]; rfl
  · rw [globalVal_Fl h (by omega) hx]; rfl

@[simp] theorem memB_setGlobalIdx (m : ModuleInst) (v : Val) :
    memB (setGlobalIdx s m x v) ma = memB s ma := by
  simp [memB]

@[simp] theorem setMem_funcs (a : Nat) (m : MemInst) : (s.setMem a m).funcs = s.funcs := rfl

@[simp] theorem setMem_globals (a : Nat) (m : MemInst) : (s.setMem a m).globals = s.globals := rfl

@[simp] theorem globalVal_setMem' (m : ModuleInst) (a : Nat) (mm : MemInst) :
    globalVal (s.setMem a mm) m x = globalVal s m x := rfl

theorem memB_setMem (hma : ma < s.mems.length) (B : ByteArray) :
    memB (s.setMem ma ⟨mt, B⟩) ma = B := by
  simp [memB, Store.setMem, hma]

@[simp] theorem setMem_mems_length (a : Nat) (m : MemInst) :
    (s.setMem a m).mems.length = s.mems.length := by
  simp [Store.setMem]

theorem good_setR (hnd : mi.globals.Nodup) (hx : x < 17) (v : BitVec 64)
    (h : Good mi ma mt fis s) : Good mi ma mt fis (setGlobalIdx s mi x (.num ⟨.int .i64, v⟩)) := by
  refine ⟨fun a ha => by simpa using h.funcs a ha, fun k hk => ?_, fun k hk hk' => ?_,
    by simpa [setGlobalIdx_mems] using h.mem, by simpa using h.size⟩
  · by_cases hkx : k = x
    · subst hkx
      exact ⟨v, by rw [globalVal_setGlobalIdx_self, globalVal_R h hk]; rfl⟩
    · rw [globalVal_setGlobalIdx_ne hnd hkx]
      exact h.regs k hk
  · rw [globalVal_setGlobalIdx_ne hnd (show k ≠ x by omega)]
    exact h.flags k hk hk'

theorem good_setF (hnd : mi.globals.Nodup) (hx : 17 ≤ x) (hx' : x < 24) (v : BitVec 32)
    (h : Good mi ma mt fis s) : Good mi ma mt fis (setGlobalIdx s mi x (.num ⟨.int .i32, v⟩)) := by
  refine ⟨fun a ha => by simpa using h.funcs a ha, fun k hk => ?_, fun k hk hk' => ?_,
    by simpa [setGlobalIdx_mems] using h.mem, by simpa using h.size⟩
  · rw [globalVal_setGlobalIdx_ne hnd (show k ≠ x by omega)]
    exact h.regs k hk
  · by_cases hkx : k = x
    · subst hkx
      exact ⟨v, by rw [globalVal_setGlobalIdx_self, globalVal_Fl h hk hk']; rfl⟩
    · rw [globalVal_setGlobalIdx_ne hnd hkx]
      exact h.flags k hk hk'

theorem good_ma (h : Good mi ma mt fis s) : ma < s.mems.length := by
  have := h.mem
  by_contra hc
  rw [List.getElem?_eq_none (by omega)] at this
  cases this

theorem good_setMem (B : ByteArray) (h : Good mi ma mt fis s) (hB : 65536 ≤ B.size) :
    Good mi ma mt fis (s.setMem ma ⟨mt, B⟩) := by
  have hma := good_ma h
  refine ⟨fun a ha => by simpa using h.funcs a ha, fun k hk => ?_, fun k hk hk' => ?_, ?_, ?_⟩
  · exact h.regs k hk
  · exact h.flags k hk hk'
  · simp [Store.setMem, hma]
  · rw [memB_setMem hma]; exact hB

/-! ## Reading back -/

theorem R_set_self (h : Good mi ma mt fis s) (hx : x < 24) (v : BitVec 64) :
    R (setGlobalIdx s mi x (.num ⟨.int .i64, v⟩)) mi x = v := by
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (good_isSome h hx)
  simp [R, globalVal_setGlobalIdx_self, hu]

theorem Fl_set_self (h : Good mi ma mt fis s) (hx : x < 24) (v : BitVec 32) :
    Fl (setGlobalIdx s mi x (.num ⟨.int .i32, v⟩)) mi x = v := by
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (good_isSome h hx)
  simp [Fl, globalVal_setGlobalIdx_self, hu]

theorem R_set_self' (hs : (globalVal s mi x).isSome) (v : BitVec 64) :
    R (setGlobalIdx s mi x (.num ⟨.int .i64, v⟩)) mi x = v := by
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hs
  simp [R, globalVal_setGlobalIdx_self, hu]

theorem Fl_set_self' (hs : (globalVal s mi x).isSome) (v : BitVec 32) :
    Fl (setGlobalIdx s mi x (.num ⟨.int .i32, v⟩)) mi x = v := by
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hs
  simp [Fl, globalVal_setGlobalIdx_self, hu]

theorem R_set_ne (hnd : mi.globals.Nodup) (hk : k ≠ x) (v : Val) :
    R (setGlobalIdx s mi x v) mi k = R s mi k := by
  simp only [R, globalVal_setGlobalIdx_ne hnd hk]

theorem Fl_set_ne (hnd : mi.globals.Nodup) (hk : k ≠ x) (v : Val) :
    Fl (setGlobalIdx s mi x v) mi k = Fl s mi k := by
  simp only [Fl, globalVal_setGlobalIdx_ne hnd hk]

@[simp] theorem R_setMem (a : Nat) (m : MemInst) : R (s.setMem a m) mi k = R s mi k := rfl
@[simp] theorem Fl_setMem (a : Nat) (m : MemInst) : Fl (s.setMem a m) mi k = Fl s mi k := rfl

/-- Memory `0` of the instance, through `memB`. -/
theorem mem?_good (h : Good mi ma mt fis s) (hm : mi.mems[0]? = some ma) (ls : List (Option Val)) :
    s.mem? ⟨ls, mi⟩ ⟨0⟩ = some (ma, ⟨mt, memB s ma⟩) := by
  have hma := good_ma h
  have hmem := h.mem
  rw [List.getElem?_eq_getElem hma] at hmem
  simp only [Option.map_some, Option.some.injEq] at hmem
  have h0 : mi.mems[(⟨0⟩ : MemIdx).toNat]? = some ma := hm
  simp [Store.mem?, h0, memB, List.getElem?_eq_getElem hma, ← hmem]

/-! ## The flag effects -/

section Flags

variable {c p a z sg o : BitVec 32}

theorem good_set6 (hnd : mi.globals.Nodup) (h : Good mi ma mt fis s) :
    Good mi ma mt fis (set6 mi s c p a z sg o) := by
  simp only [set6, Val.i32]
  repeat (first | apply good_setF hnd (by omega) (by omega) | exact h)

theorem R_set6 (hnd : mi.globals.Nodup) (hk : k < 17) : R (set6 mi s c p a z sg o) mi k = R s mi k := by
  unfold set6
  repeat rw [R_set_ne hnd (by omega)]

theorem Fl_set6_21 (hnd : mi.globals.Nodup) (h : (globalVal s mi 21).isSome) :
    Fl (set6 mi s c p a z sg o) mi 21 = sg := by
  simp only [set6, Val.i32]
  rw [Fl_set_ne hnd (by omega), Fl_set_self' (by simpa using h)]

theorem Fl_set6_22 (h : (globalVal s mi 22).isSome) :
    Fl (set6 mi s c p a z sg o) mi 22 = o := by
  simp only [set6, Val.i32]
  rw [Fl_set_self' (by simpa using h)]

@[simp] theorem memB_set6 : memB (set6 mi s c p a z sg o) ma = memB s ma := by
  simp [set6]

theorem good_cmpEff (hnd : mi.globals.Nodup) (h : Good mi ma mt fis s) (x y : BitVec 64) :
    Good mi ma mt fis (cmpEff mi s x y) := good_set6 hnd h

theorem R_cmpEff (hnd : mi.globals.Nodup) (hk : k < 17) (x y : BitVec 64) :
    R (cmpEff mi s x y) mi k = R s mi k := R_set6 hnd hk

theorem Fl_cmpEff_21 (hnd : mi.globals.Nodup) (h : (globalVal s mi 21).isSome) (x y : BitVec 64) :
    Fl (cmpEff mi s x y) mi 21 =
      Silmaril.Wasm.Numerics.bool32 (((x - y) &&& 1 <<< 63) != 0#64) := Fl_set6_21 hnd h

theorem Fl_cmpEff_22 (h : (globalVal s mi 22).isSome) (x y : BitVec 64) :
    Fl (cmpEff mi s x y) mi 22 =
      Silmaril.Wasm.Numerics.bool32 (((x ^^^ y) &&& (x ^^^ (x - y)) &&& 1 <<< 63) != 0#64) :=
  Fl_set6_22 h

@[simp] theorem isSome_cmpEff (x y : BitVec 64) :
    (globalVal (cmpEff mi s x y) mi k).isSome = (globalVal s mi k).isSome := by
  simp [cmpEff, fresEff, set6]

@[simp] theorem memB_cmpEff (x y : BitVec 64) : memB (cmpEff mi s x y) ma = memB s ma := by
  simp [cmpEff, fresEff]

end Flags

/-! ## Signed comparison from the flags -/

theorem msb_and (v : BitVec 64) : (v &&& 9223372036854775808#64 = 0#64) ↔ v.msb = false := by
  rw [show (9223372036854775808#64) = BitVec.twoPow 64 63 by decide, BitVec.msb_eq_getLsbD_last]
  constructor
  · intro h
    have := congrArg (·.getLsbD 63) h
    simpa [BitVec.getLsbD_and, BitVec.getLsbD_twoPow] using this
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    by_cases h63 : i = 63
    · subst h63; simpa [BitVec.getLsbD_eq_getElem] using h
    · simp [BitVec.getLsbD_and, BitVec.getLsbD_twoPow, Ne.symm h63]

theorem slt_flags (a b : BitVec 64) : a.slt b =
    ((a - b).msb ^^ ((a ^^^ b) &&& (a ^^^ (a - b))).msb) :=
  Silmaril.X86.Ext.slt_eq_sign_xor_overflow a b

end Silmaril.Sim.X86.Max2
