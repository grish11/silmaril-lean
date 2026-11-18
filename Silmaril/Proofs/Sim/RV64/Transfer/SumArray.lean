module

public import Silmaril.Proofs.Sim.RV64.Transfer.Generic
public import Silmaril.Sim.RV64.CfgM.Thms
public import Silmaril.WasmSpec.Rv64SumArray.Defs
public import Silmaril.Wasm.Logic.Tactic.Defs
public import Silmaril.Wasm.Logic.Instr.Thms

/-!
# `sum_array`: a loop reading memory, from its Wasm problem to the RV64 problem

Cut point `0x112d4`; blocks with loads (`cfgSymM`, `decide`). The Wasm module reads the imported
memory through the effective-address helper `$ea` (alignment and bounds checks, trapping
otherwise). **Memory window** (`MemWin`, as `Silmaril.Sim.X86.GM.MemEnc`): the RV64 process
memory reads, at every aligned in-bounds address, the doubleword of the Wasm memory bytes `B`
there (RV address = Wasm address).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Sim.RV64.Transfer.SumArray

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.RiscV.Ext
open Silmaril.Sim.RV64 Silmaril.Sim.RV64.Sym Silmaril.Sim.RV64.Cfg Silmaril.Sim.RV64.CfgM
  Silmaril.Sim.RV64.Transfer Silmaril.Wasm.Game
open Silmaril.Wasm.Logic.VC
open Silmaril.WasmSpec.Rv64SumArray (func program Pre Post)

def words : List (BitVec 32) :=
  [0x00000613, 0x00b05e63, 0x00359593, 0x00b505b3, 0x00053683, 0x00850513, 0x00c68633,
   0xfeb51ae3, 0x00060513, 0x00008067]

def cuts : List W64 := [0x112d4#64]

def T0 : TreeM := (TreeM.br (BranchOp.ge) (ME.const 0x0000000000000000#64) (ME.var 0x0b#5) (TreeM.leaf (LeafM.ret (ME.bin (Bin.add) (ME.bin (Bin.add) (ME.const 0x0000000000000000#64) (ME.const 0x0000000000000000#64)) (ME.const 0x0000000000000000#64)))) (TreeM.leaf (LeafM.goto 0x00000000000112d4#64 [ME.const 0x0000000000000000#64, ME.var 0x01#5, ME.var 0x02#5, ME.var 0x03#5, ME.var 0x04#5, ME.var 0x05#5, ME.var 0x06#5, ME.var 0x07#5, ME.var 0x08#5, ME.var 0x09#5, ME.var 0x0a#5, ME.bin (Bin.add) (ME.var 0x0a#5) (ME.bin (Bin.sll) (ME.var 0x0b#5) (ME.const 0x0000000000000003#64)), ME.bin (Bin.add) (ME.const 0x0000000000000000#64) (ME.const 0x0000000000000000#64), ME.var 0x0d#5, ME.var 0x0e#5, ME.var 0x0f#5, ME.var 0x10#5, ME.var 0x11#5, ME.var 0x12#5, ME.var 0x13#5, ME.var 0x14#5, ME.var 0x15#5, ME.var 0x16#5, ME.var 0x17#5, ME.var 0x18#5, ME.var 0x19#5, ME.var 0x1a#5, ME.var 0x1b#5, ME.var 0x1c#5, ME.var 0x1d#5, ME.var 0x1e#5, ME.var 0x1f#5])))

def T1 : TreeM := (TreeM.chk (ME.ld (ME.bin (Bin.add) (ME.var 0x0a#5) (ME.const 0x0000000000000000#64))) (TreeM.br (BranchOp.ne) (ME.bin (Bin.add) (ME.var 0x0a#5) (ME.const 0x0000000000000008#64)) (ME.var 0x0b#5) (TreeM.leaf (LeafM.goto 0x00000000000112d4#64 [ME.const 0x0000000000000000#64, ME.var 0x01#5, ME.var 0x02#5, ME.var 0x03#5, ME.var 0x04#5, ME.var 0x05#5, ME.var 0x06#5, ME.var 0x07#5, ME.var 0x08#5, ME.var 0x09#5, ME.bin (Bin.add) (ME.var 0x0a#5) (ME.const 0x0000000000000008#64), ME.var 0x0b#5, ME.bin (Bin.add) (ME.ld (ME.bin (Bin.add) (ME.var 0x0a#5) (ME.const 0x0000000000000000#64))) (ME.var 0x0c#5), ME.ld (ME.bin (Bin.add) (ME.var 0x0a#5) (ME.const 0x0000000000000000#64)), ME.var 0x0e#5, ME.var 0x0f#5, ME.var 0x10#5, ME.var 0x11#5, ME.var 0x12#5, ME.var 0x13#5, ME.var 0x14#5, ME.var 0x15#5, ME.var 0x16#5, ME.var 0x17#5, ME.var 0x18#5, ME.var 0x19#5, ME.var 0x1a#5, ME.var 0x1b#5, ME.var 0x1c#5, ME.var 0x1d#5, ME.var 0x1e#5, ME.var 0x1f#5])) (TreeM.leaf (LeafM.ret (ME.bin (Bin.add) (ME.bin (Bin.add) (ME.ld (ME.bin (Bin.add) (ME.var 0x0a#5) (ME.const 0x0000000000000000#64))) (ME.var 0x0c#5)) (ME.const 0x0000000000000000#64))))))

set_option maxRecDepth 10000 in
theorem sym0 : cfgSymM (codeAt 0x112c4 words) cuts 12 true 0x112c4#64 regs0M = some T0 := by decide

set_option maxRecDepth 10000 in
theorem sym1 : cfgSymM (codeAt 0x112c4 words) cuts 12 true 0x112d4#64 regs0M = some T1 := by decide

/-- **The memory window**: the RV64 memory `M` reads the Wasm memory bytes `B` at every aligned
in-bounds doubleword (RV address = Wasm address). -/
def MemWin (M : Silmaril.Process.Memory) (B : ByteArray) : Prop :=
  ∀ p : W64, p.toNat % 8 = 0 → p.toNat + 8 ≤ B.size → ld64 M p = Memory.load B p.toNat 8

/-- The helper `$ea`. -/
def eaFunc : Func := program.funcs[1]

/-- `$ea`'s first segment (alignment check) and the rest after `memory.size`. -/
def eaSeg1 : List Silmaril.Wasm.Instr := eaFunc.body.take 8
def eaSeg2 : List Silmaril.Wasm.Instr := eaFunc.body.drop 9

set_option maxRecDepth 10000 in
theorem ea_body : eaFunc.body = eaSeg1 ++ (.memorySize ⟨0⟩ :: eaSeg2) := rfl

/-- What `$ea a 8` guarantees when it returns, for memory bytes `B`. -/
def EaOK (B : ByteArray) (a : BitVec 64) (res : List Val) : Prop :=
  res = [.i32 (wrap64 a)] ∧ a.toNat % 8 = 0 ∧ a.toNat + 8 ≤ B.size

/-- The helper's specification (calls with width `8`). -/
def eaSpec (fe : FuncInst Nat) (ma : Nat) (mt : MemoryType) (B : ByteArray) :
    Silmaril.Wasm.Logic.Hoare.FSpec Nat where
  pre s args := s.funcs[1]? = some fe ∧ fe.module.mems[0]? = some ma ∧
    s.mems[ma]? = some ⟨mt, B⟩ ∧ 65536 ≤ B.size ∧ B.size ≤ 2 ^ 32 ∧ mt.address = .i32 ∧
    ∃ a : BitVec 64, args = [.i64 a, .i64 8]
  post s args s' o := s' = s ∧ ∀ a : BitVec 64, args = [.i64 a, .i64 8] →
    o = .trap ∨ ∃ res, o = .normal res ∧ EaOK B a res

theorem align8 (a : BitVec 64) (h : BitVec.setWidth 32 a &&& 7#32 = 0#32) : a.toNat % 8 = 0 := by
  have := congrArg BitVec.toNat h
  simp [BitVec.toNat_and] at this
  have h7 : (7 : Nat) = 2 ^ 3 - 1 := rfl
  rw [h7, Nat.and_two_pow_sub_one_eq_mod] at this
  omega

def tyEa : FnType := ⟨[.num (.int .i64), .num (.int .i64)], [.num (.int .i32)]⟩

/-- The bounds check of `$ea`: the test `a > pages * 65536 - 8` failed. -/
private theorem ea_bound {B : ByteArray} {a : BitVec 64} {mt : MemoryType}
    (hsz0 : 65536 ≤ B.size) (hsz : B.size ≤ 2 ^ 32)
    (hg : bool32 (Nat.blt ((18446744073709551608 +
      (MemInst.pages ⟨mt, B⟩ % 4294967296 % 18446744073709551616) <<< 16) %
        18446744073709551616) a.toNat) = 0#32) :
    a.toNat + 8 ≤ B.size := by
  have hp : B.size / 65536 ≤ 65536 := by omega
  have hm : B.size / 65536 * 65536 ≤ B.size := Nat.div_mul_le_self _ _
  have e1 : B.size / 65536 % 4294967296 % 18446744073709551616 = B.size / 65536 := by
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have e2 : (18446744073709551608 + B.size / 65536 * 65536) % 18446744073709551616 =
      B.size / 65536 * 65536 - 8 := by omega
  have hg' : a.toNat ≤ (18446744073709551608 + B.size / 65536 * 65536) % 18446744073709551616 := by
    simpa [bool32, MemInst.pages, Memory.pageSize, Nat.shiftLeft_eq, e1] using hg
  omega

/-- The first segment of `$ea`: the alignment check, up to `memory.size`. -/
private theorem ea_seg1 {fe : FuncInst Nat} {ma : Nat}
    {lim : Limits} {B : ByteArray} (s : Store Nat) (a : BitVec 64) :
    wpc (H := Nat) (fun _ _ _ _ => True) 0 eaSeg1 (cutQ (fun s' f' vs => s' = s ∧
        f' = Frame.forCall fe.module [Val.i64 a, Val.i64 8] eaFunc.locals ∧ vs = [.i64 a] ∧
        a.toNat % 8 = 0)
      (fnPost 1 ((eaSpec fe ma ⟨.i32, lim⟩ B).post s [Val.i64 a, Val.i64 8])))
      s (Frame.forCall fe.module [Val.i64 a, Val.i64 8] eaFunc.locals) [] := by
  simp only [eaSeg1, Func.body, eaFunc, program, Fin.isValue, Nat.reducePow,
    List.getElem_cons_succ, List.getElem_cons_zero, List.take_succ_cons, List.take_zero,
    Frame.forCall, Val.i64, BitVec.ofNat_eq_ofNat, List.map_cons, List.map_nil, Func.locals,
    List.append_nil, eaSpec, true_and, List.cons.injEq, Val.num.injEq, and_true, wpc, ctl,
    Wasm.Logic.Core.exec1, List.reverse_nil, Wasm.Logic.Core.localVal?, Frame.local?, Idx.toNat,
    Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.ofNat_pos, getElem?_pos, Option.map_some, List.reverse_cons,
    List.nil_append, Nat.one_mod, Nat.one_lt_ofNat, List.cons_append, Wasm.Logic.Core.popInt,
    Option.bind_some, Wasm.Logic.Core.intBinOp_i64_sub, BitVec.reduceSub,
    Wasm.Logic.Core.intBinOp_i64_and, cvt1, wrap64, BitVec.setWidth_and, Nat.reduceLeDiff,
    BitVec.setWidth_ofNat_of_le, popI32, ne_eq, enterVC, ModuleInst.blockType?, Std.le_refl,
    tsub_self, List.take_nil, cutQ, List.reverse_eq_cons_iff, List.drop_nil, labelQ, fnPost,
    reduceCtorEq, false_and, exists_const, or_false, implies_true, and_self]
  exact align8 a

/-- The second segment of `$ea`, after `memory.size`: the bounds check. -/
private theorem ea_seg2 {P : Profile} {host : HostSemantics Nat} {fe : FuncInst Nat} {ma : Nat}
    {lim : Limits} {B : ByteArray} {s : Store Nat} {a : BitVec 64}
    (hma : fe.module.mems[0]? = some ma)
    (hmem : s.mems[ma]? = some ⟨⟨.i32, lim⟩, B⟩) (hsz0 : 65536 ≤ B.size) (hsz : B.size ≤ 2 ^ 32)
    (h8 : a.toNat % 8 = 0) :
    Silmaril.Wasm.Logic.Hoare.TWP P host s (Frame.forCall fe.module [Val.i64 a, Val.i64 8] eaFunc.locals)
      (vals [.i64 a] ++ Admin.plain (Instr.memorySize ⟨0⟩) :: List.map Admin.plain eaSeg2)
      (fnPost 1 ((eaSpec fe ma ⟨.i32, lim⟩ B).post s [Val.i64 a, Val.i64 8])) := by
  have hl2 : loops eaSeg2 = 0 := by simp [eaSeg2, eaFunc, program, loops, ctl]
  have hm : s.mem? (Frame.forCall fe.module [Val.i64 a, Val.i64 8] eaFunc.locals) ⟨0⟩ =
      some (ma, ⟨⟨.i32, lim⟩, B⟩) := by simp [Store.mem?, Frame.forCall, Idx.toNat, hma, hmem]
  refine Silmaril.Wasm.Logic.Hoare.Wp.memorySize (m := .total) (us := [.i64 a]) hm
    (wpc_sound_total (P := P) (host := host) (fun _ _ _ _ => True) 0 eaSeg2 hl2
      (fnPost 1 ((eaSpec fe ma ⟨.i32, lim⟩ B).post s [Val.i64 a, Val.i64 8])) s
      (Frame.forCall fe.module [Val.i64 a, Val.i64 8] eaFunc.locals)
      [.i64 a, .num ⟨.int .i32, BitVec.ofNat 32 (MemInst.pages ⟨⟨.i32, lim⟩, B⟩)⟩] ?_)
  simp only [eaSeg2, Func.body, eaFunc, program, Fin.isValue, Nat.reducePow,
    List.getElem_cons_succ, List.getElem_cons_zero, List.drop_succ_cons, List.drop_zero, eaSpec,
    Val.i64, BitVec.ofNat_eq_ofNat, true_and, EaOK, Val.i32, wrap64, ↓existsAndEq,
    List.cons.injEq, Val.num.injEq, and_true, Frame.forCall, List.map_cons, List.map_nil,
    Func.locals, List.append_nil, wpc, ctl, cvt1, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, extendU32, Wasm.Logic.Core.exec1,
    Wasm.Logic.Core.popInt, Option.bind_some, Wasm.Logic.Core.intBinOp_i64_shl,
    BitVec.toNat_ofNat, Nat.reduceMod, Wasm.Logic.Core.localVal?, Frame.local?, Idx.toNat,
    Fin.coe_ofNat_eq_mod, Nat.one_mod, List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.one_lt_ofNat, getElem?_pos, Option.map_some,
    Wasm.Logic.Core.intBinOp_i64_sub, intRelOp_i64_gtU, BitVec.toNat_sub, Nat.reduceSub,
    BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, Nat.add_mod_mod, gt_iff_lt, popI32, ne_eq,
    enterVC, ModuleInst.blockType?, Std.le_refl, tsub_self, List.take_nil, Nat.zero_mod,
    List.reverse_reverse, fnPost, reduceCtorEq, Wasm.Logic.Core.Outcome.normal.injEq, false_or,
    List.drop_nil, labelQ, false_and, or_false, implies_true, and_self, Nat.ofNat_pos]
  intro hg a2 e
  have ea : a = a2 := by cases e; rfl
  rw [← ea]
  exact ⟨rfl, h8, ea_bound hsz0 hsz hg⟩

set_option maxRecDepth 10000 in
theorem ea_valid {P : Profile} {host : HostSemantics Nat} {fe : FuncInst Nat} {ma : Nat}
    {mt : MemoryType} {B : ByteArray} (hc : fe.code = .wasm eaFunc)
    (ht : FnType.ofDefType? fe.type = some tyEa) :
    Silmaril.Wasm.Logic.Hoare.FSpecValid P host 1 (eaSpec fe ma mt B) := by
  refine Silmaril.Wasm.Logic.Hoare.TFSpecAt.valid (TFSpecAt.of_fnPost (fun _ _ h => h.1) hc
    (FnType.expand_of_ofDefType? ht) (by rintro s args ⟨-, -, -, -, -, -, a, rfl⟩; rfl) ?_)
  rintro s args ⟨hfe, hma, hmem, hsz0, hsz, haddr, a, hargs⟩
  obtain ⟨addr, lim⟩ := mt
  obtain rfl : addr = .i32 := haddr
  rw [hargs, show (Validation.Ty.ofList (List.map ScalarType.toC tyEa.results)).length = 1 from rfl,
    ea_body]
  simp only [expression, List.map_append, List.map_cons]
  have hl : loops eaSeg1 = 0 := by simp [eaSeg1, eaFunc, program, loops, ctl]
  refine twp_cut (P := P) (host := host) (inv := fun _ _ _ _ => True) (k := 0) (vs := [])
    (rest := Admin.plain (Instr.memorySize ⟨0⟩) :: List.map Admin.plain eaSeg2)
    (s := s) (f := Frame.forCall fe.module [Val.i64 a, Val.i64 8] eaFunc.locals) hl
    (ea_seg1 s a) ?_
  rintro s' f' vs ⟨hs', hf', hvs, h8⟩
  rw [hs', hf', hvs]
  exact ea_seg2 hma hmem hsz0 hsz h8

/-! ## Translation validation -/

/-- The spec context: `$ea` at address `1`. -/
@[instance_reducible]
def Γea (fe : FuncInst Nat) (ma : Nat) (mt : MemoryType) (B : ByteArray) : VCSpecs Nat :=
  ⟨fun a => if a = 1 then some (2, eaSpec fe ma mt B) else none⟩

theorem Γea_specs1 (fe : FuncInst Nat) (ma : Nat) (mt : MemoryType) (B : ByteArray) :
    (Γea fe ma mt B).specs 1 = some (2, eaSpec fe ma mt B) := rfl

theorem Γea_valid {P : Profile} {host : HostSemantics Nat} {fe : FuncInst Nat} {ma : Nat}
    {mt : MemoryType} {B : ByteArray} (hc : fe.code = .wasm eaFunc)
    (ht : FnType.ofDefType? fe.type = some tyEa) : (Γea fe ma mt B).Valid P host := by
  intro a n S h
  change (if a = 1 then some (2, eaSpec fe ma mt B) else none) = some (n, S) at h
  split at h
  next ha =>
    subst ha
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨ea_valid hc ht, fun s args hp => by simp [hp.1]⟩
  next => cases h

/-- A block step, stated on the computed outcome. -/
theorem block_out {m₀ : MState} {code : Code} {cuts : List W64} {n : Nat} {pc : W64}
    {σ : Reg → W64} {T : TreeM} (hcode : ∀ p w, code p = some w → fetch m₀.memory p = some w)
    (hra : (m₀.core.read 1#5).toNat % 4 = 0)
    (hT : cfgSymM code cuts n true pc regs0M = some T) (h : Reach m₀ pc σ) :
    match T.run σ m₀.memory with
    | some o => BlockOut m₀ o
    | none => True := by
  cases ho : T.run σ m₀.memory with
  | none => trivial
  | some o => exact reach_blockM hcode hra hT h ho

/-- The simulation invariant at the Wasm loop. -/
def simInv (m₀ : MState) (s₀ : Store Nat) (mi : ModuleInst) : Invs Nat :=
  fun _ s f a => s = s₀ ∧ a = [] ∧ ∃ (σ : Reg → W64) (x : W64), Reach m₀ 0x112d4#64 σ ∧
    f = ⟨[some (.i64 (σ 10#5)), some (.i64 (σ 11#5)), some (.i64 (σ 12#5)), some (.i64 x)], mi⟩

set_option maxRecDepth 10000 in
set_option linter.unusedSimpArgs false in
theorem tv_body (m₀ : MState) (hcode : ∀ p w, codeAt 0x112c4 words p = some w → fetch m₀.memory p = some w)
    (hpc : m₀.core.pc = 0x112c4#64) (hra : (m₀.core.read 1#5).toNat % 4 = 0)
    {B : ByteArray} (hwin : MemWin m₀.memory B) (hsz0 : 65536 ≤ B.size) (hsz : B.size ≤ 2 ^ 32)
    (fe : FuncInst Nat) {ma : Nat} {mt : MemoryType} (haddr : mt.address = .i32)
    (s : Store Nat) (hs1 : s.funcs[1]? = some fe) (mi : ModuleInst)
    (hmi : mi.funcs = [0, 1]) (hmm : mi.mems[0]? = some ma) (hfm : fe.module.mems[0]? = some ma)
    (hmem : s.mems[ma]? = some ⟨mt, B⟩)
    (R : Store Nat → Silmaril.Wasm.Logic.Core.Outcome → Prop)
    (hR : ∀ v, Returns m₀ v → R s (.normal [.i64 v])) (hRt : R s .trap) :
    wpc (Γ := Γea fe ma mt B) (simInv m₀ s mi) 0 func.body (fnPost 1 R) s
      (Frame.forCall mi [.i64 (m₀.core.read 10#5), .i64 (m₀.core.read 11#5)] func.locals) [] := by
  have h0 := block_out hcode hra sym0 (hpc ▸ reach_entry m₀)
  simp [T0, TreeM.run, ME.eval, Bin.eval, LeafM.vals, BranchOp.eval, BlockOut, BitVec.slt] at h0
  simp [func, program, wpc, ctl, enterVC, labelQ, loopQ, popI32, Silmaril.Wasm.Logic.Core.exec1,
    Silmaril.Wasm.Logic.Core.popInt, Silmaril.Wasm.Logic.Core.popV, Silmaril.Wasm.Logic.Core.localVal?,
    Frame.local?, Frame.setLocal, Frame.forCall, ModuleInst.blockType?, Idx.toNat, Val.i64,
    Val.i32, simInv, defaultVal_i64, intRelOp_i64_geS, intRelOp_i64_ne, bool32, fnPost]
  refine ⟨fun hz => ?_, fun hz => ⟨?_, ?_⟩⟩
  · rw [ite_eq_left (by omega)] at h0
    simpa [Val.i64] using hR _ h0
  · rw [ite_eq_right (by omega)] at h0
    exact ⟨_, h0, by simp, by simp, by simp, _, rfl⟩
  rintro s' f' rfl σ hσ x rfl -
  have h1 := block_out hcode hra sym1 hσ
  simp [T1, TreeM.run, ME.eval, Bin.eval, LeafM.vals, BranchOp.eval, BlockOut] at h1
  simp [callVC, Γea_specs1, hmi, eaSpec, hs1, hfm, hmem, hsz0, hsz, haddr, callK, Idx.toNat]
  refine ⟨⟨hsz, ⟨_, rfl⟩, rfl⟩, ?_⟩
  rintro s1 o rfl hpost
  rcases hpost (σ 10#5) rfl rfl with rfl | ⟨res, rfl, hres, hal, hbd⟩
  · simpa [loopQ, labelQ, fnPost] using hRt
  subst hres
  have hlt : (σ 10#5).toNat < 2 ^ 32 := by omega
  have hw : (wrap64 (σ 10#5)).toNat = (σ 10#5).toNat := by
    simp [wrap64, BitVec.toNat_setWidth]; omega
  obtain ⟨w, hw8⟩ : ∃ w, Memory.load B (σ 10#5).toNat 8 = some w :=
    ⟨_, Silmaril.Wasm.Logic.Core.load_eq (by omega)⟩
  have hld : ld64 m₀.memory (σ 10#5) = some w := by rw [hwin _ hal hbd, hw8]
  have hm1 : ∀ ls, s1.mem? ⟨ls, mi⟩ ⟨0⟩ = some (ma, ⟨mt, B⟩) := by
    intro ls; simp [Store.mem?, Idx.toNat, hmm, hmem]
  have hmod : (σ 10#5).toNat % 4294967296 = (σ 10#5).toNat := Nat.mod_eq_of_lt hlt
  simp [Val.i32, Val.i64, hm1, hw, hmod, effAddr, IntType.width, hw8, Silmaril.Wasm.Logic.Core.exec1,
    Silmaril.Wasm.Logic.Core.popInt, Silmaril.Wasm.Logic.Core.popV, Silmaril.Wasm.Logic.Core.localVal?,
    Frame.local?, Frame.setLocal, intRelOp_i64_ne, bool32, wpc, ctl, loopQ, labelQ, enterVC,
    ModuleInst.blockType?, popI32, fnPost]
  simp [hld] at h1
  refine ⟨fun hne => ?_, fun he => ?_⟩
  · rw [ite_eq_right hne] at h1
    exact ⟨_, h1, by simp, by simp, by simp, _, rfl⟩
  · rw [ite_eq_left he] at h1
    simpa [Val.i64] using hR _ h1

end Silmaril.Sim.RV64.Transfer.SumArray
