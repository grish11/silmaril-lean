module

public import Silmaril.Wasm.Examples.JsonAccept.Defs
public import Silmaril.Wasm.Verify.FnSpec.Thms
public import Silmaril.Formats.JsonBytes.Thms
public import Mathlib.Tactic.IntervalCases

/-!
# A concrete Wasm acceptor for a JSON subset: proofs

* `spec_vc` is the verification condition of `accept`, for the `wpc` generator of
  `Silmaril.Wasm.Logic.VC`. It runs as `wasm_vc` does, but with an explicit `simp` step bound and
  the frame unfolded. After the generator has reduced the loop body to arithmetic, the loop step
  is checked by kernel evaluation (`decide`) over the 6 states and all 256 byte values.
* `rest_of_acc` (soundness) and `acc_of_intText` (completeness) show that the automaton accepts
  exactly `intText`. `intText_le_language`: integer texts are JSON texts.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Examples.JsonAccept

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Verify Silmaril.Wasm.Logic.Words
open Silmaril.Formats.JsonBytes Silmaril.Wasm.Examples.JsonAccept
open scoped Computability

/-! ## The module meets its specification -/

/-- A one-byte load is `bd` in bounds and fails out of bounds. -/
theorem load1_ite (B : ByteArray) (a : Nat) :
    Execution.Memory.load B a 1 = if a + 1 ≤ B.size then some (bd B a) else none := by
  split
  · unfold bd
    rw [Silmaril.Wasm.Logic.Core.load_eq ‹_›]; rfl
  · exact Silmaril.Wasm.Logic.Core.load_eq_none (B := B) (a := a) (n := 1) (by omega)

theorem bytesN_succ (B : ByteArray) (a k : Nat) :
    bytesN B a (k + 1) = bytesN B a k ++ [(bd B (a + k)).toNat] := by
  simp [bytesN, List.range_succ]

theorem runN_append_single (q : Nat) (bs : List Nat) (b : Nat) :
    runN q (bs ++ [b]) = stepN (runN q bs) b := by
  simp [runN, List.foldl_append]

theorem tbl_lt (q c : Nat) : tbl q c < 6 := by
  unfold tbl; split <;> omega

theorem runN_lt {q : Nat} (hq : q < 6) (bs : List Nat) : runN q bs < 6 := by
  induction bs generalizing q with
  | nil => exact hq
  | cons b bs ih => exact ih (tbl_lt _ _)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
set_option linter.unusedSimpArgs false in
/-- **`accept` meets `spec`.** -/
theorem spec_vc : spec.vc prog.funcs[0] := by
  simp only [Silmaril.Wasm.Verify.FnSpec.vc, Silmaril.Wasm.Verify.FnSpec.mem,
    Silmaril.Wasm.Logic.Words.MemAt, spec, prog]
  simp (maxSteps := 100000000) [Silmaril.Wasm.Logic.VC.wpc, Silmaril.Wasm.Logic.VC.ctl,
    Silmaril.Wasm.Logic.VC.loops, Silmaril.Wasm.Logic.VC.enterVC, Silmaril.Wasm.Logic.VC.labelQ,
    Silmaril.Wasm.Logic.VC.loopQ, Silmaril.Wasm.Logic.VC.popI32,
    Silmaril.Wasm.Execution.Core.Frame.forCall, Silmaril.Wasm.Examples.Common.bodyPost,
    Silmaril.Wasm.Execution.Core.ModuleInst.blockType?, Silmaril.Wasm.Logic.VC.defaultVal_i32,
    wat_vc_simp, -Silmaril.Wasm.Logic.Core.intTestOp_eqz,
    Silmaril.Wasm.Execution.Core.Store.mem?, Silmaril.Wasm.Execution.Core.effAddr,
    Silmaril.Wasm.IntType.width, load1_ite, Silmaril.Wasm.PackSize.width]
  intro p n mi s ma mt B hm0 hm hpre1 hpre2
  refine ⟨fun _ _ _ _ _ => by simp [bytesN, runN], ?_⟩
  intro s' f' hs i q b c hloc hle hinv hmod
  subst hs hmod
  obtain ⟨locals, module⟩ := f'
  simp only at hloc hinv ⊢
  subst hloc
  simp (maxSteps := 100000000) [Silmaril.Wasm.Logic.VC.wpc, Silmaril.Wasm.Logic.VC.ctl,
    Silmaril.Wasm.Logic.VC.loops, Silmaril.Wasm.Logic.VC.enterVC, Silmaril.Wasm.Logic.VC.labelQ,
    Silmaril.Wasm.Logic.VC.loopQ, Silmaril.Wasm.Logic.VC.popI32,
    Silmaril.Wasm.Examples.Common.bodyPost, wat_vc_simp, -Silmaril.Wasm.Logic.Core.intTestOp_eqz,
    Silmaril.Wasm.Execution.Core.Store.mem?, Silmaril.Wasm.Execution.Core.effAddr,
    Silmaril.Wasm.IntType.width, load1_ite, Silmaril.Wasm.PackSize.width]
  simp only at hm0
  refine ⟨fun hin ma' mt' B' h1 h2 => ?_, fun hne => ?_⟩
  · rw [hm0] at h1; cases h1
    rw [hm] at h2; cases h2
    refine ⟨(Silmaril.Wasm.Verify.setMem_eq_self hm).symm, ?_⟩
    have hq := hinv ma mt B hm0 hm
    subst hin
    generalize hk : runN 0 (bytesN B p.toNat i.toNat) = k at hq
    have hk6 : k < 6 := hk ▸ runN_lt (by decide) _
    subst hq
    clear hinv hk
    interval_cases k <;> decide
  have hlt : i.toNat < n.toNat := lt_of_le_of_ne hle (fun h => hne (BitVec.eq_of_toNat_eq h))
  have h1 : (p.toNat + i.toNat) % 4294967296 = p.toNat + i.toNat := Nat.mod_eq_of_lt (by omega)
  have hb : p.toNat + i.toNat + 1 ≤ B.size := by omega
  simp only [hm0, hm, Option.bind_some, h1, hb, ↓reduceIte]
  simp (maxSteps := 100000000) [Silmaril.Wasm.Logic.VC.wpc, Silmaril.Wasm.Logic.VC.ctl,
    Silmaril.Wasm.Logic.VC.loops, Silmaril.Wasm.Logic.VC.enterVC, Silmaril.Wasm.Logic.VC.labelQ,
    Silmaril.Wasm.Logic.VC.loopQ, Silmaril.Wasm.Logic.VC.popI32,
    wat_vc_simp, -Silmaril.Wasm.Logic.Core.intTestOp_eqz,
    Silmaril.Wasm.Execution.Core.Store.mem?, Silmaril.Wasm.Execution.Core.effAddr,
    Silmaril.Wasm.IntType.width, load1_ite, Silmaril.Wasm.PackSize.width]
  refine ⟨by omega, fun ma' mt' B' h1' h2' => ?_⟩
  rw [hm0] at h1'; cases h1'
  rw [hm] at h2'; cases h2'
  have hq := hinv ma mt B hm0 hm
  rw [show (i.toNat + 1) % 4294967296 = i.toNat + 1 from Nat.mod_eq_of_lt (by omega), bytesN_succ,
    runN_append_single]
  generalize hk : runN 0 (bytesN B p.toNat i.toNat) = k at hq
  have hk6 : k < 6 := hk ▸ runN_lt (by decide) _
  subst hq
  generalize bd B (p.toNat + i.toNat) = v
  clear hinv hk
  interval_cases k <;> revert v <;> decide

/-! ## The automaton accepts exactly the integer texts -/

theorem eq_of_toNat {b : UInt8} {n : Nat} (h : b.toNat = n) (hn : n < 256 := by omega) :
    b = UInt8.ofNat n := UInt8.toNat_inj.1 (by simp [h, Nat.mod_eq_of_lt hn])

theorem rest_cons (q : Nat) (b : UInt8) (w : List UInt8) (h : Rest (stepN q b.toNat) w) :
    Rest q (b :: w) := by
  have hb := b.toNat_lt
  unfold stepN cls at h
  rcases q with _ | _ | _ | _ | _ | q
  · split_ifs at h with h0 h1 h2 h3 <;> simp only [tbl, Rest] at h
    · obtain ⟨a, v, c, rfl, ha, hv, hc⟩ := h
      refine ⟨b :: a, v, c, rfl, ?_, hv, hc⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · rcases h0 with h | h | h | h <;> rw [eq_of_toNat h] <;> simp [IsWsByte]
      · exact ha x hx
    · obtain ⟨i, c, rfl, hi, hc⟩ := h
      refine ⟨[], b :: i, c, by simp, by simp, ⟨[b], i, rfl, .inr (by rw [eq_of_toNat h1]; rfl), hi⟩, hc⟩
    · refine ⟨[], [b], w, by simp, by simp, ⟨[], [b], rfl, .inl rfl, .inl (by rw [eq_of_toNat h2]; rfl)⟩, h⟩
    · obtain ⟨ds, c, rfl, hds, hc⟩ := h
      refine ⟨[], b :: ds, c, by simp, by simp, ⟨[], b :: ds, rfl, .inl rfl, .inr ⟨b, ds, rfl, ?_, hds⟩⟩, hc⟩
      constructor <;> rw [UInt8.le_iff_toNat_le] <;> simp <;> omega
  · split_ifs at h with h0 h1 h2 h3 <;> simp only [tbl, Rest] at h
    · exact ⟨[b], w, rfl, .inl (by rw [eq_of_toNat h2]; rfl), h⟩
    · obtain ⟨ds, c, rfl, hds, hc⟩ := h
      refine ⟨b :: ds, c, rfl, .inr ⟨b, ds, rfl, ?_, hds⟩, hc⟩
      constructor <;> rw [UInt8.le_iff_toNat_le] <;> simp <;> omega
  · split_ifs at h with h0 h1 h2 h3 <;> simp only [tbl, Rest] at h
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · rcases h0 with h | h | h | h <;> rw [eq_of_toNat h] <;> simp [IsWsByte]
    · exact h x hx
  · split_ifs at h with h0 h1 h2 h3 <;> simp only [tbl, Rest] at h
    · refine ⟨[], b :: w, rfl, by simp, ?_⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · rcases h0 with h | h | h | h <;> rw [eq_of_toNat h] <;> simp [IsWsByte]
      · exact h x hx
    · obtain ⟨ds, c, rfl, hds, hc⟩ := h
      refine ⟨b :: ds, c, rfl, ?_, hc⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · rw [eq_of_toNat h2]; unfold IsDigit; decide
      · exact hds x hx
    · obtain ⟨ds, c, rfl, hds, hc⟩ := h
      refine ⟨b :: ds, c, rfl, ?_, hc⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · constructor <;> rw [UInt8.le_iff_toNat_le] <;> simp <;> omega
      · exact hds x hx
  · split_ifs at h with h0 h1 h2 h3 <;> simp only [tbl, Rest] at h
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · rcases h0 with h | h | h | h <;> rw [eq_of_toNat h] <;> simp [IsWsByte]
    · exact h x hx
  · split_ifs at h <;> simp [tbl, Rest] at h

/-- **Soundness of the automaton**: an accepting run reads what `Rest` allows. -/
theorem rest_of_acc (q : Nat) (w : List UInt8) (h : 2 ≤ runN q (w.map UInt8.toNat) ∧
    runN q (w.map UInt8.toNat) ≤ 4) : Rest q w := by
  induction w generalizing q with
  | nil =>
    simp only [List.map_nil, runN, List.foldl_nil] at h
    obtain ⟨h1, h2⟩ := h
    interval_cases q
    · simp [Rest]
    · exact ⟨[], [], rfl, by simp, by simp⟩
    · simp [Rest]
  | cons b w ih =>
    exact rest_cons q b w (ih _ h)

theorem cls_ws {b : UInt8} (h : IsWsByte b) : cls b.toNat = 0 := by
  rcases h with rfl | rfl | rfl | rfl <;> decide

theorem cls_digit {b : UInt8} (h : IsDigit b) : cls b.toNat = 2 ∨ cls b.toNat = 3 := by
  obtain ⟨h1, h2⟩ := h
  rw [UInt8.le_iff_toNat_le] at h1 h2
  simp only [UInt8.toNat_ofNat] at h1 h2
  unfold cls; split_ifs <;> omega

theorem cls_digit19 {b : UInt8} (h : IsDigit19 b) : cls b.toNat = 3 := by
  obtain ⟨h1, h2⟩ := h
  rw [UInt8.le_iff_toNat_le] at h1 h2
  simp only [UInt8.toNat_ofNat] at h1 h2
  unfold cls; split_ifs <;> omega

theorem runN_cons (q : Nat) (b : UInt8) (w : List UInt8) :
    runN q ((b :: w).map UInt8.toNat) = runN (stepN q b.toNat) (w.map UInt8.toNat) := rfl

theorem ws_rest4 : ∀ (w : List UInt8), (∀ x ∈ w, IsWsByte x) →
    runN 4 (w.map UInt8.toNat) = 4
  | [], _ => rfl
  | b :: w, h => by
    rw [runN_cons, stepN, cls_ws (h b (by simp))]
    exact ws_rest4 w (fun x hx => h x (by simp [hx]))

theorem digits_rest3 : ∀ (ds c : List UInt8), (∀ x ∈ ds, IsDigit x) → (∀ x ∈ c, IsWsByte x) →
    2 ≤ runN 3 ((ds ++ c).map UInt8.toNat) ∧ runN 3 ((ds ++ c).map UInt8.toNat) ≤ 4
  | [], [], _, _ => by decide
  | [], b :: c, _, hc => by
    rw [List.nil_append, runN_cons, stepN, cls_ws (hc b (by simp))]
    simp only [tbl]
    rw [ws_rest4 c (fun x hx => hc x (by simp [hx]))]; decide
  | d :: ds, c, hd, hc => by
    rw [List.cons_append, runN_cons, stepN]
    rcases cls_digit (hd d (by simp)) with h | h <;> rw [h] <;> simp only [tbl] <;>
      exact digits_rest3 ds c (fun x hx => hd x (by simp [hx])) hc

theorem int_rest1 {i c : List UInt8} (hi : IntLex i) (hc : ∀ x ∈ c, IsWsByte x) (q : Nat)
    (hq : ∀ b : UInt8, cls b.toNat = 2 ∨ cls b.toNat = 3 → stepN q b.toNat = tbl 1 (cls b.toNat)) :
    2 ≤ runN q ((i ++ c).map UInt8.toNat) ∧ runN q ((i ++ c).map UInt8.toNat) ≤ 4 := by
  rcases hi with rfl | ⟨d, ds, rfl, hd, hds⟩
  · rw [List.cons_append, List.nil_append, runN_cons,
      hq 48 (.inl (by decide))]
    show 2 ≤ runN 2 _ ∧ runN 2 _ ≤ 4
    rcases c with _ | ⟨b, c⟩
    · decide
    · rw [runN_cons, stepN, cls_ws (hc b (by simp))]
      simp only [tbl]
      rw [ws_rest4 c (fun x hx => hc x (by simp [hx]))]; decide
  · rw [List.cons_append, runN_cons, hq d (.inr (cls_digit19 hd)), cls_digit19 hd]
    exact digits_rest3 ds c hds hc

/-- **Completeness of the automaton for the subset**: it accepts every integer text. -/
theorem acc_of_intText {w : List UInt8} (h : w ∈ intText) :
    2 ≤ runN 0 (w.map UInt8.toNat) ∧ runN 0 (w.map UInt8.toNat) ≤ 4 := by
  obtain ⟨a, v, c, rfl, ha, ⟨m, i, rfl, hm, hi⟩, hc⟩ := h
  induction a with
  | nil =>
    rcases hm with rfl | rfl
    · simp only [List.nil_append]
      exact int_rest1 hi hc 0 fun b hb => by
        rcases hb with hb | hb <;> simp [stepN, hb, tbl]
    · simp only [List.nil_append, List.cons_append]
      rw [runN_cons, show stepN 0 (UInt8.toNat 45) = 1 by decide]
      exact int_rest1 hi hc 1 fun b _ => rfl
  | cons b a ih =>
    rw [List.cons_append, List.cons_append, runN_cons, stepN, cls_ws (ha b (by simp))]
    exact ih (fun x hx => ha x (by simp [hx]))

/-! ## Integer texts are JSON texts -/

theorem digits_mem_kstar {ds : List UInt8} (h : ∀ x ∈ ds, IsDigit x) :
    ds ∈ digit.matches'∗ := by
  rw [Language.mem_kstar]
  refine ⟨ds.map fun x => [x], ?_, ?_⟩
  · clear h
    induction ds with
    | nil => rfl
    | cons x xs ih => simp only [List.map_cons, List.flatten_cons, List.singleton_append, ← ih]
  intro y hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
  exact Silmaril.Formats.Utf8.mem_byteRange.2 ⟨x, rfl, (h x hx).1, (h x hx).2⟩

theorem intLex_mem {i : List UInt8} (h : IntLex i) :
    i ∈ Silmaril.Formats.JsonBytes.int.matches' := by
  simp only [Silmaril.Formats.JsonBytes.int, RegularExpression.matches'_add,
    RegularExpression.matches'_mul, RegularExpression.matches'_char, RegularExpression.matches'_star,
    Language.mem_add, Language.mem_mul]
  rcases h with rfl | ⟨d, ds, rfl, hd, hds⟩
  · exact .inl rfl
  · exact .inr ⟨[d], Silmaril.Formats.Utf8.mem_byteRange.2 ⟨d, rfl, hd.1, hd.2⟩, ds,
      digits_mem_kstar hds, rfl⟩

theorem numLex_mem {v : List UInt8} (h : NumLex v) : v ∈ number.matches' := by
  obtain ⟨m, i, rfl, hm, hi⟩ := h
  simp only [number, RegularExpression.matches'_mul, Language.mem_mul]
  refine ⟨m ++ i, ⟨m ++ i, ⟨m, ?_, i, intLex_mem hi, rfl⟩, [], ?_, by simp⟩, [], ?_, by simp⟩
  · rcases hm with rfl | rfl
    · exact Or.inl Language.nil_mem_one
    · simp only [RegularExpression.matches'_add, RegularExpression.matches'_char, Language.mem_add]
      exact .inr rfl
  · simp only [RegularExpression.matches'_add, RegularExpression.matches'_epsilon, Language.mem_add]
    exact Or.inl Language.nil_mem_one
  · simp only [RegularExpression.matches'_add, RegularExpression.matches'_epsilon, Language.mem_add]
    exact Or.inl Language.nil_mem_one

/-- **The integer texts are JSON texts**, under either escape profile. -/
theorem intText_le_language (p : Profile) : intText ≤ language p := by
  rintro w ⟨a, v, c, rfl, ha, hv, hc⟩
  refine ⟨a, v, c, mem_ws.2 ha, .scalar ?_, mem_ws.2 hc, rfl⟩
  simp only [scalar, RegularExpression.matches'_add, Language.mem_add]
  exact .inl (.inr (numLex_mem hv))

end Silmaril.Proofs.Wasm.Examples.JsonAccept
