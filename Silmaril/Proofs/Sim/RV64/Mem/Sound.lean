module

public import Silmaril.Proofs.Sim.RV64.Mem.Step

/-!
# The memory-state RV64 simulator: soundness of `step`

* `wb_state`: the write-back of `step` is the reference `Silmaril.RiscV.step` on the abstraction;
* `absCode_of_sameOutside`: writes to the register block do not change the code;
* **`step_sound`**: `step` meets `stepSpec` (total correctness, every profile and host relation).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Sim.RV64.Mem

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.VC Silmaril.Sim.RV64 Silmaril.Wasm.Logic.Words
open Silmaril.Wasm.Logic.Core (leNat bytesAt Post Outcome storeLE)
open Silmaril.RiscV (decode State)

variable {H : Type}

/-! ## The write-back and the frame -/

theorem bytesAt_of_sameOutside {B B' : ByteArray} (h : SameOutside B B' 0 256)
    (r : Silmaril.Wasm.Logic.Core.Region) (hr : 256 ≤ r.base) : bytesAt B' r = bytesAt B r := by
  apply List.ext_getElem?
  intro i
  rw [Silmaril.Wasm.Logic.Core.getElem?_bytesAt, Silmaril.Wasm.Logic.Core.getElem?_bytesAt]
  split
  · exact h.2 _ (Or.inr (by omega))
  · rfl

/-- Writes confined to the register block leave the code (and `code_end`) unchanged. -/
theorem absCode_of_sameOutside {B B' : ByteArray} (h : SameOutside B B' 0 256) :
    absCode B' = absCode B := by
  have he : ld64 B' 264 = ld64 B 264 := by
    simp only [ld64, bytesAt_of_sameOutside h ⟨264, 8⟩ (by decide)]
  have hce : codeEnd B' = codeEnd B := by simp only [codeEnd, he]
  funext pc
  simp only [absCode, hce]
  split_ifs with hc
  · simp only [ld32, bytesAt_of_sameOutside h ⟨pc.toNat, 4⟩ (by simp; omega)]
  · rfl

theorem wf_of_sameOutside {B B' : ByteArray} (h : SameOutside B B' 0 256) (hB : WF B) : WF B' := by
  unfold WF at *; rw [h.1]; exact hB

theorem wb_same {B : ByteArray} (hB : WF B) {rd : BitVec 32} (hrd : rd.toNat < 32)
    (v pc : BitVec 64) : SameOutside B (wb B rd v pc) 0 256 := by
  unfold WF at hB
  unfold wb
  have h1 : SameOutside B (if rd = 0#32 then B else storeLE B (rd.toNat * 8) 8 v.toNat) 0 256 := by
    split
    · exact SameOutside.refl B 0 256
    · exact sameOutside_storeLE v (by omega) (by omega) (by omega)
  refine h1.trans (sameOutside_storeLE _ (by rw [h1.1]; omega) (by omega) (by omega))

/-- **The write-back is the reference retirement.** -/
theorem wb_state {B : ByteArray} (hB : WF B) {w : BitVec 32} {i : Silmaril.RiscV.Instr} (hd : decode w = some i) :
    absState (wb B ((w >>> 7) % 32#32) (i.value (absState B)) (ld64 B 0)) =
      Silmaril.RiscV.step i (absState B) := by
  have hB0 : 65536 ≤ B.size := hB
  have hdest : i.dest = w.extractLsb' 7 5 := dest_of_decode hd
  have hrd : ((w >>> 7) % 32#32).toNat = i.dest.toNat := by rw [hdest, reg_toNat]
  have hdlt : i.dest.toNat < 2 ^ 5 := i.dest.isLt
  set σ := absState B
  set v := i.value σ
  set B1 := if (w >>> 7) % 32#32 = 0#32 then B else storeLE B (((w >>> 7) % 32#32).toNat * 8) 8 v.toNat
  have hB1 : B1.size = B.size := by
    simp only [B1]; split
    · rfl
    · exact size_storeLE _ (by omega)
  have hz : ((w >>> 7) % 32#32 = 0#32) ↔ i.dest = 0#5 := by
    rw [← BitVec.toNat_inj, ← BitVec.toNat_inj, hrd]; simp
  simp only [wb]
  change absState (storeLE B1 0 8 (ld64 B 0 + 4#64).toNat) = _
  simp only [Silmaril.RiscV.step, absState, State.mk.injEq]
  refine ⟨?_, ld64_storeLE_same _ (by omega)⟩
  funext r
  simp only [State.write, σ]
  by_cases hr : r = 0#5
  · rw [hr]
    by_cases hd0 : i.dest = 0#5
    · simp [hd0, absState]
    · simp [hd0, absState, Silmaril.Machine.RegisterFile.write, Ne.symm hd0]
  · show (if r = 0#5 then 0 else ld64 (storeLE B1 0 8 (ld64 B 0 + 4#64).toNat) (8 * r.toNat)) =
      (if i.dest = 0#5 then absState B
        else ({ regs := (absState B).regs.write i.dest v, pc := (absState B).pc } : State)).regs r
    have hrlt : r.toNat < 2 ^ 5 := r.isLt
    have hr8 : 1 ≤ r.toNat := by
      rcases Nat.eq_zero_or_pos r.toNat with h | h
      · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hr
      · exact h
    rw [ite_eq_right hr, ld64_storeLE_ne _ (by omega) (by omega) (by omega)]
    by_cases hd0 : i.dest = 0#5
    · have : B1 = B := by simp only [B1, hz.mpr hd0, ite_true]
      simp [hd0, this, absState, hr]
    · show ld64 B1 (8 * r.toNat) = (if i.dest = 0#5 then absState B
        else ({ regs := (absState B).regs.write i.dest v, pc := (absState B).pc } : State)).regs r
      have hB1e : B1 = storeLE B (i.dest.toNat * 8) 8 v.toNat := by
        simp only [B1, mt hz.mp hd0, ite_false, hrd]
      rw [hB1e]
      simp only [hd0, ite_false, Silmaril.Machine.RegisterFile.write]
      by_cases hrd' : r = i.dest
      · rw [hrd']
        simp only [ite_true]
        rw [show 8 * i.dest.toNat = i.dest.toNat * 8 by omega]
        exact ld64_storeLE_same _ (by omega)
      · have hne : r.toNat ≠ i.dest.toNat := fun h => hrd' (BitVec.eq_of_toNat_eq h)
        rw [ite_eq_right hrd', ld64_storeLE_ne _ (by omega) (by omega) (by omega)]
        simp [absState, hr]

/-! ## Soundness of `step` -/

theorem loops_segF : loops segF = 0 := by
  simp [segF, stepFunc, simM, loops, ctl]
theorem loops_segD : loops segD = 0 := by
  simp [segD, stepFunc, simM, loops, ctl]
theorem loops_segX : loops segX = 0 := by
  simp [segX, stepFunc, simM, loops, ctl]

theorem expression_append (l₁ l₂ : List Silmaril.Wasm.Instr) :
    expression (l₁ ++ l₂) = expression l₁ ++ expression l₂ := List.map_append

variable {P : Profile} {host : HostSemantics H}

/-- **Soundness of `step`**: every call of the function `step` (code `stepFunc`, type
`[] → [i32]`) at address `a`, from a store whose memory `0` holds a well-formed `B`, terminates
and returns a status `st` with the memory now `B'` and `StepPost B st B'`; at every profile and
for every host relation. -/
theorem step_sound {fi : FuncInst H} {a ma : Nat} {mt : MemoryType} {B : ByteArray}
    {ps rs : Silmaril.Wasm.Validation.Ty (.list .val)} (hcode : fi.code = .wasm stepFunc)
    (he : Silmaril.Wasm.Validation.Expand fi.type (.func ps rs)) (hps : ps.length = 0)
    (hrs : rs.length = 1) :
    Silmaril.Wasm.Logic.Hoare.TFSpecAt P host a (stepSpec fi a ma mt B) := by
  refine TFSpecAt.of_fnPost (fun _ _ h => h.1) hcode he (fun _ _ h => by rw [h.2.1, hps]; rfl) ?_
  intro s args hpre
  obtain ⟨-, hargs, hm, hB⟩ : s.funcs[a]? = some fi ∧ args = [] ∧ MemAt s fi.module ma mt B ∧
      WF B := hpre
  rw [hargs]
  have hB' : 65536 ≤ B.size := hB
  set σ := absState B with hσ
  set Q : Post H := fnPost rs.length ((stepSpec fi a ma mt B).post s [])
  -- the exits with status 2 and 3
  have hstop : ∀ (st : BitVec 32), (st = 2 ∨ st = 3) → refStep (absCode B) σ = none →
      ∀ f, Q s f (.ret [.num ⟨.int .i32, st⟩]) := by
    intro st hst hn f
    simp only [Q, fnPost, hrs, List.length_cons, List.length_nil, Nat.le_refl, true_and,
      Nat.sub_self, List.drop_zero]
    exact ⟨st, B, rfl, (MemAt.setMem_self hm).symm, .inr ⟨hst, rfl, hn⟩⟩
  have hσpc : σ.pc = ld64 B 0 := rfl
  rw [body_eq, expression_append]
  show Silmaril.Wasm.Logic.Hoare.TWP P host s _ (vals [] ++ (expression segF ++ _)) Q
  refine twp_cut loops_segF (C := fun s' f vs => s' = s ∧ vs = [] ∧ ∃ w,
      absCode B (ld64 B 0) = some w ∧
      f = frm fi.module (ld64 B 0) (ld64 B 264) w (w.setWidth 64) 0 0 0 0)
    (segF_vc s fi.module ma mt B hm hB' _ Q
      (fun hn => hstop 3 (.inr rfl) (by simp [refStep, hσpc, hn]))
      (fun w hw => ⟨rfl, rfl, w, hw, rfl⟩)) ?_
  intro s' f vs hC
  obtain ⟨hs, hvs, w, hw, hf⟩ : s' = s ∧ vs = [] ∧ ∃ w, absCode B (ld64 B 0) = some w ∧
      f = frm fi.module (ld64 B 0) (ld64 B 264) w (w.setWidth 64) 0 0 0 0 := hC
  rw [hs, hvs, hf, expression_append]
  show Silmaril.Wasm.Logic.Hoare.TWP P host s
    (frm fi.module (ld64 B 0) (ld64 B 264) w (w.setWidth 64) 0 0 0 0)
    (vals [] ++ (expression segD ++ expression (segX ++ segW))) Q
  refine twp_cut loops_segD (C := fun s' f vs => s' = s ∧ vs = [] ∧
      f = frm fi.module (ld64 B 0) (ld64 B 264) w (w.setWidth 64) ((w >>> 7) % 32#32)
        (σ.read (w.extractLsb' 15 5)) (σ.read (w.extractLsb' 20 5)) 0)
    (segD_vc s fi.module ma mt B hm hB' _ _ w _ Q ⟨rfl, rfl, rfl⟩) ?_
  intro s' f vs hC
  obtain ⟨hs, hvs, hf⟩ : s' = s ∧ vs = [] ∧
      f = frm fi.module (ld64 B 0) (ld64 B 264) w (w.setWidth 64) ((w >>> 7) % 32#32)
        (σ.read (w.extractLsb' 15 5)) (σ.read (w.extractLsb' 20 5)) 0 := hC
  rw [hs, hvs, hf, expression_append]
  show Silmaril.Wasm.Logic.Hoare.TWP P host s
    (frm fi.module (ld64 B 0) (ld64 B 264) w (w.setWidth 64) ((w >>> 7) % 32#32)
      (σ.read (w.extractLsb' 15 5)) (σ.read (w.extractLsb' 20 5)) 0)
    (vals [] ++ (expression segX ++ expression segW)) Q
  refine twp_cut loops_segX (C := fun s' f vs => s' = s ∧ vs = [] ∧ ∃ i,
      decode w = some i ∧
      f = frm fi.module (ld64 B 0) (ld64 B 264) w (w.setWidth 64) ((w >>> 7) % 32#32)
        (σ.read (w.extractLsb' 15 5)) (σ.read (w.extractLsb' 20 5)) (i.value σ))
    (segX_vc s fi.module _ _ w _ σ hσpc _ Q
      (fun hn => hstop 2 (.inl rfl) (by simp [refStep, hσpc, hw, hn]))
      (fun i hi => ⟨rfl, rfl, i, hi, rfl⟩)) ?_
  intro s' f vs hC
  obtain ⟨hs, hvs, i, hi, hf⟩ : s' = s ∧ vs = [] ∧ ∃ i, decode w = some i ∧
      f = frm fi.module (ld64 B 0) (ld64 B 264) w (w.setWidth 64) ((w >>> 7) % 32#32)
        (σ.read (w.extractLsb' 15 5)) (σ.read (w.extractLsb' 20 5)) (i.value σ) := hC
  rw [hs, hvs, hf]
  have hrd : ((w >>> 7) % 32#32).toNat < 32 := by
    rw [reg_toNat]; exact (w.extractLsb' 7 5).isLt
  have hW : wpc (fun _ _ _ _ => True) 0 segW (fnPost 1 ((stepSpec fi a ma mt B).post s [])) s
      (frm fi.module (ld64 B 0) (ld64 B 264) w (w.setWidth 64) ((w >>> 7) % 32#32)
        (σ.read (w.extractLsb' 15 5)) (σ.read (w.extractLsb' 20 5)) (i.value σ)) [] := segW_vc s fi.module ma mt B hm hB' (ld64 B 0) (ld64 B 264) (w.setWidth 64)
    (σ.read (w.extractLsb' 15 5)) (σ.read (w.extractLsb' 20 5)) (i.value σ) w _ hrd
    ((stepSpec fi a ma mt B).post s [])
    ⟨0, _, rfl, rfl, .inl ⟨rfl, by
      simp only [refStep, hσ, show (absState B).pc = ld64 B 0 from rfl, hw, hi, Option.bind_some,
        Option.map_some, wb_state hB hi], wb_same hB hrd _ _⟩⟩
  simpa [Q, hrs] using wpc_sound_total (P := P) (host := host) _ 0 segW
    (by simp [segW, stepFunc, simM, loops, ctl]) _ _ _ _ hW

end Silmaril.Sim.RV64.Mem
