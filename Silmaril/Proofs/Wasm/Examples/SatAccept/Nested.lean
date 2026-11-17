module

public import Silmaril.Proofs.Wasm.Examples.SatAccept.Stream

/-!
# The SAT acceptor: `check-nested`

`nested_vc`: `check-nested` meets `nestedSpec`, as `stream_vc`: the clause loop reads the pair
`(ptr, len)` of clause `i` (`addr8`, `addr8'`), the literal loop its words, the scan the model;
the answer is `satNested_eq`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Examples.SatAccept

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Verify Silmaril.Wasm.Logic.Words
open Silmaril.Wasm.Examples.SatAccept
open Silmaril.Wasm.Logic.VC (globalVal setGlobalIdx)

set_option hygiene false in
/-- The generator's simplification for `check-nested`, with the hypotheses of `nested_vc`. -/
macro "nested_simp" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  sat_simp [hg, hm0, hm, nestedInv, locs, checkPost, MemAt, mem0, forall_store_eq,
    forall_store_eq₂, forall_params_nil, forall_frame_module, forall_locals_swap, forall_memAt hm,
    bool32_true, bool32_false, litWord_eq, intMin_eq, $ls,*])

/-- The address of the pair `i` of an array of pairs at `p` (`p + (i << 3)`, no wrapping). -/
theorem addr8 {p i : BitVec 32} {n : Nat} (hi : i.toNat < n) (hb : p.toNat + 8 * n ≤ memBytes) :
    (p + i <<< 3).toNat = p.toNat + 8 * i.toNat := by
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  simp only [memBytes] at hb
  have : i.toNat * 2 ^ 3 % 2 ^ 32 = 8 * i.toNat := Nat.mod_eq_of_lt (by omega) |>.trans (by ring)
  omega

/-- The address of the second word of pair `i`. -/
theorem addr8' {p i : BitVec 32} {n : Nat} (hi : i.toNat < n) (hb : p.toNat + 8 * n ≤ memBytes) :
    (p + (i <<< 3 + 4#32)).toNat = p.toNat + 8 * i.toNat + 4 := by
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  simp only [memBytes] at hb
  have : i.toNat * 2 ^ 3 % 2 ^ 32 = 8 * i.toNat := Nat.mod_eq_of_lt (by omega) |>.trans (by ring)
  simp only [BitVec.toNat_ofNat]
  omega

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem nested_vc : nestedSpec.vc prog.funcs[2] := by
  simp only [Silmaril.Wasm.Verify.FnSpec.vc, nestedSpec, prog, checkPre]
  rintro ⟨pp, pl, mp, ml⟩ mi s ⟨⟨ma, mt, B, ⟨hm0, hm⟩, hsz, ⟨hN, hNi⟩, hM⟩, hg⟩
  obtain ⟨g, hg⟩ := Option.isSome_iff_exists.1 hg
  simp only at hN hNi hM
  nested_simp []
  refine ⟨by simp [modelPre_zero, bool32_true], ?_⟩
  intro i j k hit x y has cp cl hi
  refine ⟨fun hexit => ?_, fun hcont => ?_⟩
  · -- after the model loop
    subst i
    refine ⟨rfl, ?_⟩
    intro i j k hit x y has cp cl hi
    refine ⟨fun hexit => ?_, fun hcont => ?_⟩
    · subst i
      rw [satNested_eq, length_words, List.take_of_length_le (by simp), bool32_ite]
    · -- the clause loop body
      have hlt : i.toNat < pl.toNat := lt_of_le_of_ne hi (fun h => hcont (BitVec.eq_of_toNat_eq h))
      have ha := addr8 (p := pp) (i := i) hlt (by omega)
      simp only [ha, show pp.toNat + 8 * i.toNat + 4 ≤ B.size by omega, ↓reduceIte]
      nested_simp []
      have hcl := addr8' (p := pp) (i := i) hlt (by omega)
      simp only [hcl, show pp.toNat + 8 * i.toNat + 4 + 4 ≤ B.size by omega, ↓reduceIte]
      nested_simp []
      refine ⟨hlt, ?_⟩
      intro i j k x y has hi hk
      have hC := hNi i.toNat hi
      refine ⟨fun hexit => ?_, fun hcont => ?_⟩
      · -- the literal loop exits: the clause is done
        subst k
        rw [succ_toNat hi]
        refine ⟨?_, by omega⟩
        rw [all_take_succ (C := nestedAt B pp.toNat pl.toNat) (k := i.toNat) (by simpa using hi) [],
          getD_nestedAt hi, List.take_of_length_le (l := wordsAt B (wd B (pp.toNat + 8 * i.toNat)).toNat
            (wd B (pp.toNat + 8 * i.toNat + 4)).toNat) (by simp)]
        simp [clauseOk, Bool.and_assoc]
      · -- the literal loop body
        have hlt' : k.toNat < (wd B (pp.toNat + 8 * i.toNat + 4)).toNat :=
          lt_of_le_of_ne hk (fun h => hcont (BitVec.eq_of_toNat_eq h))
        have ha := addr4 (p := wd B (pp.toNat + 8 * i.toNat)) (i := k) hlt' (by omega)
        have hw := wd_eq_words (B := B) (p := (wd B (pp.toNat + 8 * i.toNat)).toNat) hlt'
        simp only [ha, show (wd B (pp.toNat + 8 * i.toNat)).toNat + 4 * k.toNat + 4 ≤ B.size by omega,
          ↓reduceIte]
        nested_simp [hw]
        refine ⟨⟨?_, hi, hlt'⟩, ?_⟩
        · rw [all_take_succ (C := wordsAt B (wd B (pp.toNat + 8 * i.toNat)).toNat
            (wd B (pp.toNat + 8 * i.toNat + 4)).toNat) (k := k.toNat) (by simpa using hlt') 0]
          simp [litWord_eq, Bool.and_assoc]
        intro i j k y has hi hk hj
        have hC := hNi i.toNat hi
        refine ⟨fun hexit => ?_, fun hcont => ?_⟩
        · -- the scan exits: the literal is done
          subst j
          rw [succ_toNat hk]
          refine ⟨⟨rfl, ?_⟩, hi, by omega⟩
          rw [any_take_succ (C := wordsAt B (wd B (pp.toNat + 8 * i.toNat)).toNat
            (wd B (pp.toNat + 8 * i.toNat + 4)).toNat) (k := k.toNat) (by simpa using hk),
            List.take_of_length_le (l := wordsAt B mp.toNat ml.toNat) (by simp)]
          simp
        · -- the scan body
          have hlt'' : j.toNat < ml.toNat :=
            lt_of_le_of_ne hj (fun h => hcont (BitVec.eq_of_toNat_eq h))
          have ha := addr4 (p := mp) (i := j) hlt'' (by omega)
          have hw := wd_eq_words (B := B) (p := mp.toNat) hlt''
          simp only [ha, show mp.toNat + 4 * j.toNat + 4 ≤ B.size by omega, ↓reduceIte]
          nested_simp [hw]
          rw [succ_toNat hlt'', bool32_or, ← mem_take_succ_bool (M := wordsAt B mp.toNat ml.toNat)
            (j := j.toNat) (by simpa using hlt''), Bool.or_assoc]
          refine ⟨rfl, ?_⟩
          omega
  · -- the model loop body
    have hlt : i.toNat < ml.toNat := lt_of_le_of_ne hi (fun h => hcont (BitVec.eq_of_toNat_eq h))
    have ha := addr4 (p := mp) (i := i) hlt (by omega)
    have hw := wd_eq_words (B := B) (p := mp.toNat) hlt
    simp only [ha, show mp.toNat + 4 * i.toNat + 4 ≤ B.size by omega, ↓reduceIte]
    nested_simp [hw]
    refine ⟨hlt, ?_⟩
    intro i j k hit cp cl hi hj
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
      nested_simp [hw]
      rw [succ_toNat hlt', bool32_or, ← mem_take_succ_bool (M := wordsAt B mp.toNat ml.toNat)
        (j := j.toNat) (by simpa using hlt')]
      exact ⟨rfl, hi, by omega⟩

end Silmaril.Proofs.Wasm.Examples.SatAccept
