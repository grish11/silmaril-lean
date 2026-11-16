module

public import Silmaril.Proofs.Sim.RV64.Mem.Lemmas

/-!
# The memory-state RV64 simulator: `step` is sound

`step_sound`: the function `step` of `simM`, wherever it is instantiated (any function address,
any module instance, any memory), meets `stepSpec` with **total correctness** at every profile
and for every host relation: every call terminates and returns a status; status `0` retires
exactly the reference step `refStep (absCode B) (absState B)` of the fetched, decoded word and
changes only the register block, status `2`/`3` leaves memory unchanged where the reference
machine stops.

The body is verified in four segments with cut predicates (`Silmaril.Wasm.Logic.VC.twp_cut`):
fetch (`segF`, five fault checks and two loads of the word), operands (`segD`), the dispatch over
the 21 instructions (`segX`, one `block`) and the write-back (`segW`); each segment's condition
is computed by `wpc` and discharged by `simp` plus the decoding lemmas of
`Silmaril.Proofs.Sim.RV64.Mem.Lemmas`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Sim.RV64.Mem

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.VC Silmaril.Sim.RV64 Silmaril.Wasm.Logic.Words
open Silmaril.Wasm.Logic.Core (leNat bytesAt Post Outcome storeLE)
open Silmaril.RiscV (decode Instr State ImmOp RegOp ShiftOp UpperOp boolWord)

/- The segment conditions are evaluated with one generic `wpc` simp set. -/
set_option linter.unusedSimpArgs false

variable {H : Type}

/-! ## The segments of the body -/

/-- Fetch: load `pc` and `code_end`, the five fault checks, load the word twice. -/
def segF : List Silmaril.Wasm.Instr := stepFunc.body.take 38
/-- Operands: `rd`, `x[rs1]`, `x[rs2]`. -/
def segD : List Silmaril.Wasm.Instr := (stepFunc.body.drop 38).take 40
/-- Dispatch: one `block` computing the result `v` or returning `2`. -/
def segX : List Silmaril.Wasm.Instr := (stepFunc.body.drop 78).take 1
/-- Write-back: `x[rd] := v` unless `rd = 0`, `pc := pc + 4`, status `0`. -/
def segW : List Silmaril.Wasm.Instr := stepFunc.body.drop 79

theorem body_eq : stepFunc.body = segF ++ (segD ++ (segX ++ segW)) := by
  have h1 := List.take_append_drop 1 (stepFunc.body.drop 78)
  have h2 := List.take_append_drop 40 (stepFunc.body.drop 38)
  simp only [List.drop_drop, Nat.reduceAdd] at h1 h2
  simp only [segF, segD, segX, segW, h1, h2, List.take_append_drop]

/-- The memory after the write-back of `step`. -/
def wb (B : ByteArray) (rd : BitVec 32) (v pc : BitVec 64) : ByteArray :=
  storeLE (if rd = 0#32 then B else storeLE B (rd.toNat * 8) 8 v.toNat) 0 8 (pc + 4#64).toNat

/-- The five fetch checks of `segF` all pass: the `pc` is a well-formed code address. -/
private theorem segF_ok {B : ByteArray} (h0 : bool32 (ld64 B 0 % 4#64 != 0#64) = 0#32)
    (h1 : bool32 (decide ((ld64 B 0).toNat < 4096)) = 0#32)
    (h2 : bool32 (decide (65536 < (ld64 B 264).toNat)) = 0#32)
    (h4 : bool32 (decide (65532 < (ld64 B 0).toNat)) = 0#32)
    (h5 : bool32 (decide ((ld64 B 264).toNat < ((ld64 B 0).toNat + 4) % 18446744073709551616))
      = 0#32) :
    (ld64 B 0).toNat % 4 = 0 ∧ 4096 ≤ (ld64 B 0).toNat ∧ (ld64 B 0).toNat + 4 ≤ codeEnd B ∧
      codeEnd B ≤ 65536 := by
  have a0 : ld64 B 0 % 4#64 = 0#64 := by simpa using h0
  have a1 : 4096 ≤ (ld64 B 0).toNat := by simpa using h1
  have a2 : (ld64 B 264).toNat ≤ 65536 := by simpa using h2
  have a4 : (ld64 B 0).toNat ≤ 65532 := by simpa using h4
  have a5 : ((ld64 B 0).toNat + 4) % 18446744073709551616 ≤ (ld64 B 264).toNat := by
    simpa using h5
  have a0' : (ld64 B 0).toNat % 4 = 0 := by
    simpa [BitVec.toNat_umod] using congrArg BitVec.toNat a0
  exact ⟨a0', a1, by unfold codeEnd; omega, a2⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
theorem segF_vc (s : Store H) (mi : ModuleInst) (ma : Nat) (mt : MemoryType) (B : ByteArray)
    (hm : MemAt s mi ma mt B) (hB : 65536 ≤ B.size) (C : Store H → Frame → List Val → Prop)
    (Q : Post H) (h3 : absCode B (ld64 B 0) = none → ∀ f, Q s f (.ret [.num ⟨.int .i32, 3#32⟩]))
    (hc : ∀ w : BitVec 32, absCode B (ld64 B 0) = some w →
      C s (frm mi (ld64 B 0) (ld64 B 264) w (w.setWidth 64) 0 0 0 0) []) :
    wpc (fun _ _ _ _ => True) 0 segF (cutQ C Q) s (Frame.forCall mi [] stepFunc.locals) [] := by
  simp only [segF, Func.body, stepFunc, simM, Fin.isValue, Nat.reducePow, List.getElem_cons_zero,
    List.take_succ_cons, List.take_zero, Frame.forCall, List.map_nil, Func.locals, List.map_cons,
    defaultVal_i64, BitVec.ofNat_eq_ofNat, defaultVal_i32, List.nil_append, wpc, ctl,
    Silmaril.Wasm.Logic.Core.exec1, List.reverse_nil, List.reverse_cons, Silmaril.Wasm.Logic.Core.popInt,
    IntType.width, memq hm, Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq, effAddr,
    Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero, load8, Option.map_ite, Option.bind_some,
    BitVec.toNat_ofNat, zero_add, show 8 ≤ B.size by omega, ↓reduceIte, Silmaril.Wasm.Logic.Core.popV,
    Silmaril.Wasm.Idx.toNat, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.ofNat_pos,
    Frame.setLocal, List.set_cons_zero, Nat.reduceMod, show 272 ≤ B.size by omega, Nat.one_mod,
    Nat.one_lt_ofNat, List.set_cons_succ, Silmaril.Wasm.Logic.Core.localVal?, Frame.local?,
    getElem?_pos, Option.map_some, List.cons_append, ne_eq, BitVec.reduceEq, not_false_eq_true,
    ib_remu64, intRelOp_i64_ne, popI32, enterVC, ModuleInst.blockType?, zero_le, tsub_zero,
    List.take_length, loops, List.reverse_reverse, List.reverse_append, intRelOp_i64_ltU,
    intRelOp_i64_gtU, gt_iff_lt, Silmaril.Wasm.Logic.Core.intBinOp_i64_add, load4, PackSize.width, cutQ,
    List.drop_length, labelQ, true_and, List.append_nil, List.getElem_cons_succ, BitVec.toNat_add,
    show 4 ≤ B.size by omega]
  have none_of : ¬ ((ld64 B 0).toNat % 4 = 0 ∧ 4096 ≤ (ld64 B 0).toNat ∧
      (ld64 B 0).toNat + 4 ≤ (ld64 B 264).toNat ∧ (ld64 B 264).toNat ≤ 65536) →
      ∀ f, Q s f (.ret [.num ⟨.int .i32, 3#32⟩]) :=
    fun h => h3 (by simp only [absCode, codeEnd, h, ↓reduceIte])
  refine ⟨fun h => none_of ?_ _, fun h0 => ⟨fun h => none_of ?_ _, fun h1 => ⟨fun h => none_of ?_ _,
    fun h2 => ⟨fun h => none_of ?_ _, fun h4 => ⟨fun h => none_of ?_ _, fun h5 => ?_⟩⟩⟩⟩⟩
  · have hb : ld64 B 0 % 4#64 ≠ 0#64 := by simpa using h
    rintro ⟨ha, -⟩
    exact hb (BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_umod]; exact ha))
  · have hb : (ld64 B 0).toNat < 4096 := by simpa using h
    omega
  · have hb : 65536 < (ld64 B 264).toNat := by simpa using h
    omega
  · have hb : 65532 < (ld64 B 0).toNat := by simpa using h
    omega
  · have hb : (ld64 B 264).toNat < ((ld64 B 0).toNat + 4) % 18446744073709551616 := by simpa using h
    omega
  · have hok : (ld64 B 0).toNat % 4 = 0 ∧ 4096 ≤ (ld64 B 0).toNat ∧
        (ld64 B 0).toNat + 4 ≤ codeEnd B ∧ codeEnd B ≤ 65536 := segF_ok h0 h1 h2 h4 h5
    have hlo : (ld32 B 0).toNat = (ld64 B 0).toNat := ld32_zero_toNat B (by omega) (by omega)
    simp only [hlo, show (ld64 B 0).toNat + 4 ≤ B.size by omega, ↓reduceIte, List.reverse_nil,
      List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT, List.set_cons_succ,
      List.set_cons_zero, Option.bind_some, Fin.isValue, memq hm, show 4 ≤ B.size by omega]
    exact hc _ (by simp only [absCode, hok, and_self, ↓reduceIte])

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
theorem segD_vc (s : Store H) (mi : ModuleInst) (ma : Nat) (mt : MemoryType) (B : ByteArray)
    (hm : MemAt s mi ma mt B) (hB : 65536 ≤ B.size) (pc en : BitVec 64) (w : BitVec 32)
    (C : Store H → Frame → List Val → Prop) (Q : Post H)
    (hc : C s (frm mi pc en w (w.setWidth 64) ((w >>> 7) % 32#32)
      ((absState B).read (w.extractLsb' 15 5)) ((absState B).read (w.extractLsb' 20 5)) 0) []) :
    wpc (fun _ _ _ _ => True) 0 segD (cutQ C Q) s (frm mi pc en w (w.setWidth 64) 0 0 0 0) [] := by
  have hreg : ∀ x : Nat, x % 32 * 8 % 4294967296 + 8 ≤ B.size := fun x => by omega
  simp [segD, stepFunc, simM, cutQ, frm, Silmaril.Wasm.Logic.VC.wpc, Silmaril.Wasm.Logic.VC.ctl,
        Silmaril.Wasm.Logic.VC.popI32, Silmaril.Wasm.Logic.VC.popSelect, Silmaril.Wasm.Logic.Core.exec1,
        Silmaril.Wasm.Logic.Core.popInt, Silmaril.Wasm.Logic.Core.popV, Silmaril.Wasm.Logic.Core.localVal?,
        Silmaril.Wasm.Execution.Core.Frame.local?, Silmaril.Wasm.Execution.Core.Frame.setLocal,
        Silmaril.Wasm.Idx.toNat, Silmaril.Wasm.Logic.VC.intTestOp_i32,
        memq hm, load8, effAddr, IntType.width, hreg, Val.i32]
  rw [read_reg, read_reg] at hc
  refine ⟨fun h1 => ⟨fun h2 => ?_, fun h2 => ?_⟩, fun h1 => ⟨fun h2 => ?_, fun h2 => ?_⟩⟩ <;>
    simpa [h1, h2, frm] using hc

/-- Closes one arm of the `segX` dispatch: an undecodable word returns status `2` (`h2`), an
impossible bit pattern is refuted, and otherwise `hc` at the decoded instruction gives the
computed result, up to the arithmetic identity of its `Instr.value`. -/
local macro "segX_close " h2:ident hc:ident hpc:ident : tactic => `(tactic| first
    | (exact $h2 (by simp [decode, op_iff, f3_iff, f7_iff, f6_iff, *]) _)
    | (exfalso; bv_omega)
    | (simp [decode, op_iff, f3_iff, f7_iff, f6_iff, *] at $hc:ident
       simp only [Instr.value, ImmOp.eval, RegOp.eval, ShiftOp.eval, UpperOp.eval, boolWord, bw_slt,
         bw_ult, $hpc:ident] at $hc:ident
       refine frm_v ?_ $hc
       first
         | rfl
         | (split_ifs <;> first | rfl | omega)
         | (congr 1; simp [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]; omega)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
theorem segX_vc (s : Store H) (mi : ModuleInst) (pc en : BitVec 64) (w rd : BitVec 32)
    (σ : State) (hpc : σ.pc = pc)
    (C : Store H → Frame → List Val → Prop) (Q : Post H)
    (h2 : decode w = none → ∀ f, Q s f (.ret [.num ⟨.int .i32, 2#32⟩]))
    (hc : ∀ i, decode w = some i → C s (frm mi pc en w (w.setWidth 64) rd
      (σ.read (w.extractLsb' 15 5)) (σ.read (w.extractLsb' 20 5)) (i.value σ)) []) :
    wpc (fun _ _ _ _ => True) 0 segX (cutQ C Q) s (frm mi pc en w (w.setWidth 64) rd
      (σ.read (w.extractLsb' 15 5)) (σ.read (w.extractLsb' 20 5)) 0) [] := by
  simp only [segX, Func.body, stepFunc, simM, Fin.isValue, Nat.reducePow, List.getElem_cons_zero,
    List.drop_succ_cons, List.drop_zero, List.take_succ_cons, List.take_zero, frm,
    BitVec.ofNat_eq_ofNat, wpc, ctl, enterVC, ModuleInst.blockType?, List.length_nil, Std.le_refl,
    tsub_self, List.take_nil, loops, add_zero, cutQ, List.drop_nil, Silmaril.Wasm.Logic.Core.exec1,
    List.reverse_nil, Silmaril.Wasm.Logic.Core.localVal?, Frame.local?, Idx.toNat,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod, List.length_cons, zero_add, Nat.reduceAdd, Nat.reduceLT,
    getElem?_pos, List.getElem_cons_succ, Option.map_some, List.reverse_cons, List.nil_append,
    List.cons_append, Silmaril.Wasm.Logic.Core.popInt, IntType.width, Option.bind_some, ne_eq,
    BitVec.reduceEq, not_false_eq_true, ib_remu32, Val.i32, Silmaril.Wasm.Logic.Core.intRelOp_i32_eq,
    popI32, bool32_eq_zero, beq_eq_false_iff_ne, Decidable.not_not, List.reverse_reverse,
    List.reverse_append, zero_le, tsub_zero, List.take_length, labelQ, List.drop_length,
    Nat.zero_mod, Silmaril.Wasm.Logic.Core.intBinOp_i64_shl, BitVec.toNat_ofNat, ib_shrs64,
    Silmaril.Wasm.Logic.Core.intBinOp_i64_add, Silmaril.Wasm.Logic.Core.popV, Frame.setLocal,
    Nat.one_mod, List.length_append, List.length_reverse, List.drop_length_add_append, true_and,
    List.append_nil, Silmaril.Wasm.Logic.Core.intBinOp_i32_shrU, List.append_assoc,
    Silmaril.Wasm.Logic.Core.intBinOp_i64_sub, Silmaril.Wasm.Logic.Core.intBinOp_i64_and,
    Silmaril.Wasm.Logic.Core.intBinOp_i64_or, Silmaril.Wasm.Logic.Core.intBinOp_i64_shrU,
    Silmaril.Wasm.Logic.Core.intBinOp_i64_xor, intRelOp_i64_ltU, popSelect, intRelOp_i64_ltS,
    ib_remu64, imm_eq, Nat.lt_add_one, ↓reduceIte, List.set_cons_succ, List.set_cons_zero,
    decide_eq_false_iff_not, not_lt, not_le, BitVec.toNat_umod, BitVec.toNat_ushiftRight,
    BitVec.toNat_setWidth, dvd_refl, Nat.mod_mod_of_dvd, up_eq, Nat.ofNat_pos]
  repeat' (first | apply And.intro | intro)
  all_goals segX_close h2 hc hpc

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
theorem segW_vc (s : Store H) (mi : ModuleInst) (ma : Nat) (mt : MemoryType) (B : ByteArray)
    (hm : MemAt s mi ma mt B) (hB : 65536 ≤ B.size) (pc en w64 a b v : BitVec 64) (w rd : BitVec 32)
    (hrd : rd.toNat < 32) (R : Store H → Outcome → Prop)
    (hR : R (s.setMem ma ⟨mt, wb B rd v pc⟩) (.normal [.num ⟨.int .i32, 0#32⟩])) :
    wpc (fun _ _ _ _ => True) 0 segW (fnPost 1 R) s (frm mi pc en w w64 rd a b v) [] := by
  have hreg : rd.toNat * 8 % 4294967296 = rd.toNat * 8 := by omega
  simp [segW, stepFunc, simM, fnPost, frm, Silmaril.Wasm.Logic.VC.wpc, Silmaril.Wasm.Logic.VC.ctl,
        Silmaril.Wasm.Logic.VC.enterVC, Silmaril.Wasm.Logic.VC.labelQ, Silmaril.Wasm.Logic.VC.loops,
        Silmaril.Wasm.Execution.Core.ModuleInst.blockType?,
        Silmaril.Wasm.Logic.VC.popI32, Silmaril.Wasm.Logic.Core.exec1,
        Silmaril.Wasm.Logic.Core.popInt, Silmaril.Wasm.Logic.Core.popV, Silmaril.Wasm.Logic.Core.localVal?,
        Silmaril.Wasm.Execution.Core.Frame.local?, Silmaril.Wasm.Execution.Core.Frame.setLocal,
        Silmaril.Wasm.Idx.toNat, IntType.width, Val.i32, memq hm, mem?_setMem hm, setMem_setMem,
        store_ite, effAddr, hreg, show rd.toNat * 8 + 8 ≤ B.size by omega, show 8 ≤ B.size by omega]
  have hs1 : (storeLE B (rd.toNat * 8) 8 v.toNat).size = B.size := size_storeLE _ (by omega)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simpa [hs1, show 8 ≤ B.size by omega, wb, h] using hR
  · simpa [wb, h] using hR

end Silmaril.Sim.RV64.Mem
