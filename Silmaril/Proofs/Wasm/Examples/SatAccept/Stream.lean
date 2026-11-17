module

public import Silmaril.Proofs.Wasm.Examples.SatAccept.Basic
public import Silmaril.Proofs.Wasm.Examples.SatAccept.Lists

/-!
# The SAT acceptor: `check-stream`

`stream_vc`: `check-stream` meets `streamSpec`. The condition of `wpc` is evaluated by
`stream_simp` one loop body at a time: each memory load is resolved by its address
(`addr4`, `wd_eq_words`) from the loop bounds, and each invariant is re-established by the
one-word steps of `Silmaril.Proofs.Wasm.Examples.SatAccept.Lists` (`modelPre_succ`,
`mem_take_succ_bool`, `streamRun_take_succ`); the answer is `stream_answer`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Examples.SatAccept

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Verify Silmaril.Wasm.Logic.Words
open Silmaril.Wasm.Examples.SatAccept
open Silmaril.Wasm.Logic.VC (globalVal setGlobalIdx)

set_option hygiene false in
/-- The generator's simplification for `check-stream`, with the hypotheses of `stream_vc`. -/
macro "stream_simp" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  sat_simp [hg, hm0, hm, streamInv, locs, checkPost, MemAt, mem0, forall_store_eq,
    forall_store_eq₂, forall_params_nil, forall_frame_module, forall_locals_swap, forall_memAt hm,
    bool32_true, bool32_false, litWord_eq, intMin_eq, $ls,*])

/-- Word `k` of the segment `words B p n` read at `p + 4 k`. -/
theorem wd_eq_words {B : ByteArray} {p n k : Nat} (h : k < n) :
    wd B (p + 4 * k) = (wordsAt B p n)[k]?.getD 0 := by
  rw [getElem?_words h]; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem stream_vc : streamSpec.vc prog.funcs[1] := by
  simp only [Silmaril.Wasm.Verify.FnSpec.vc, streamSpec, prog, checkPre]
  rintro ⟨pp, pl, mp, ml⟩ mi s ⟨⟨ma, mt, B, ⟨hm0, hm⟩, hsz, hP, hM⟩, hg⟩
  obtain ⟨g, hg⟩ := Option.isSome_iff_exists.1 hg
  simp only at hP hM
  stream_simp []
  refine ⟨by simp [modelPre_zero, bool32_true], ?_⟩
  intro i j x y has hi
  refine ⟨fun hexit => ?_, fun hcont => ?_⟩
  · -- after the model loop
    subst i
    refine ⟨by simp [streamRun_nil, bool32_false], ?_⟩
    intro i j x y has hi
    refine ⟨fun hexit => ?_, fun hcont => ?_⟩
    · subst i
      refine ⟨fun hpl => ?_, fun hpl => ?_⟩
      · have hpl' : pl.toNat ≠ 0 := fun e => hpl (BitVec.eq_of_toNat_eq (by simpa using e))
        have ha := addr4 (p := pp) (i := pl - 1#32) (n := pl.toNat)
          (by rw [pred_toNat hpl]; omega) (by omega)
        rw [pred_toNat hpl] at ha
        simp only [ha, show pp.toNat + 4 * (pl.toNat - 1) + 4 ≤ B.size by omega, ↓reduceIte]
        stream_simp []
        rw [stream_answer, bool32_ite]
        simp [hpl']
      · subst hpl
        rw [stream_answer, bool32_ite]
        simp
    · -- the stream loop body
      have hlt : i.toNat < pl.toNat := lt_of_le_of_ne hi (fun h => hcont (BitVec.eq_of_toNat_eq h))
      have ha := addr4 (p := pp) (i := i) hlt (by omega)
      have hw := wd_eq_words (B := B) (p := pp.toNat) hlt
      simp only [ha, show pp.toNat + 4 * i.toNat + 4 ≤ B.size by omega, ↓reduceIte]
      stream_simp [hw]
      refine ⟨fun hx0 => ?_, fun hx0 => ⟨⟨hlt, hx0⟩, ?_⟩⟩
      · rw [succ_toNat hlt]
        refine ⟨⟨?_, ?_⟩, by omega⟩
        · simp [streamRun_take_succ (M := wordsAt B mp.toNat ml.toNat) (P := wordsAt B pp.toNat pl.toNat)
            (i := i.toNat) (by simpa using hlt), streamStep, hx0, Bool.and_assoc]
        · simp [streamRun_take_succ (M := wordsAt B mp.toNat ml.toNat) (P := wordsAt B pp.toNat pl.toNat)
            (i := i.toNat) (by simpa using hlt), streamStep, hx0, bool32_false]
      · intro i j x' a hi hj hx0
        refine ⟨fun hexit => ?_, fun hcont => ?_⟩
        · subst j
          rw [succ_toNat hi]
          refine ⟨⟨?_, ?_⟩, by omega⟩
          · simp [streamRun_take_succ (M := wordsAt B mp.toNat ml.toNat)
              (P := wordsAt B pp.toNat pl.toNat) (i := i.toNat) (by simpa using hi), streamStep, hx0,
              Bool.and_assoc, intMin_eq]
          · simp [streamRun_take_succ (M := wordsAt B mp.toNat ml.toNat)
              (P := wordsAt B pp.toNat pl.toNat) (i := i.toNat) (by simpa using hi), streamStep, hx0,
              List.take_of_length_le]
        · have hlt' : j.toNat < ml.toNat :=
            lt_of_le_of_ne hj (fun h => hcont (BitVec.eq_of_toNat_eq h))
          have ha := addr4 (p := mp) (i := j) hlt' (by omega)
          have hw := wd_eq_words (B := B) (p := mp.toNat) hlt'
          simp only [ha, show mp.toNat + 4 * j.toNat + 4 ≤ B.size by omega, ↓reduceIte]
          stream_simp [hw]
          rw [succ_toNat hlt', bool32_or, ← mem_take_succ_bool (M := wordsAt B mp.toNat ml.toNat)
            (j := j.toNat) (by simpa using hlt'), Bool.or_assoc]
          exact ⟨rfl, hi, by omega, hx0⟩
  · -- the model loop body
    have hlt : i.toNat < ml.toNat := lt_of_le_of_ne hi (fun h => hcont (BitVec.eq_of_toNat_eq h))
    have ha := addr4 (p := mp) (i := i) hlt (by omega)
    have hw := wd_eq_words (B := B) (p := mp.toNat) hlt
    simp only [ha, show mp.toNat + 4 * i.toNat + 4 ≤ B.size by omega, ↓reduceIte]
    stream_simp [hw]
    refine ⟨hlt, ?_⟩
    intro i j hi hj
    refine ⟨fun hexit => ?_, fun hcont => ?_⟩
    · subst j
      have hi1 := succ_toNat hi
      simp only [hi1]
      refine ⟨?_, by omega⟩
      rw [modelPre_succ (by simpa using hi)]
      rw [List.take_of_length_le (by simp)]
      simp [litWord_eq, Bool.and_assoc]
    · have hlt' : j.toNat < ml.toNat := lt_of_le_of_ne hj (fun h => hcont (BitVec.eq_of_toNat_eq h))
      have ha := addr4 (p := mp) (i := j) hlt' (by omega)
      have hw := wd_eq_words (B := B) (p := mp.toNat) hlt'
      simp only [ha, show mp.toNat + 4 * j.toNat + 4 ≤ B.size by omega, ↓reduceIte]
      stream_simp [hw]
      rw [succ_toNat hlt', bool32_or, ← mem_take_succ_bool (M := wordsAt B mp.toNat ml.toNat)
        (j := j.toNat) (by simpa using hlt')]
      exact ⟨rfl, hi, by omega⟩

end Silmaril.Proofs.Wasm.Examples.SatAccept
