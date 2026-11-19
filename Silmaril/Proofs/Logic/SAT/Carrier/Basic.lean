module

public import Silmaril.Logic.SAT.Carrier.Defs
public import Silmaril.Logic.SAT.CNF.Thms
public import Silmaril.Logic.SAT.LRAT.Thms
public import Mathlib.Data.List.Induction

/-! Proofs for `Silmaril.Logic.SAT.Carrier.Thms`: words, the two carriers, their languages and
the acceptors. -/

@[expose] public section

namespace Silmaril.Proofs.Logic.SAT.Carrier

open Silmaril.Logic.SAT Silmaril.Logic.SAT.Carrier

/-! ## Words -/

theorem two_pow_31 : (2 : Int) ^ 31 = 2147483648 := by decide

theorem toInt_bounds (x : S32) : -2147483648 ≤ x.toInt ∧ x.toInt < 2147483648 := by
  have h1 := BitVec.le_toInt x
  have h2 := @BitVec.toInt_lt 32 x
  simp only [show 32 - 1 = 31 from rfl, two_pow_31] at h1 h2
  exact ⟨h1, h2⟩

theorem toInt_intMin : (BitVec.intMin 32).toInt = -2147483648 := by
  rw [BitVec.toInt_intMin_of_pos (by decide)]
  decide

theorem toInt_eq_zero_iff (x : S32) : x.toInt = 0 ↔ x = 0 := by
  rw [← BitVec.toInt_inj]
  simp

theorem toInt_eq_intMin_iff (x : S32) : x.toInt = -2147483648 ↔ x = BitVec.intMin 32 := by
  rw [← BitVec.toInt_inj, toInt_intMin]

/-- A word other than `Int32.MIN` reads as an integer in range. -/
theorem inRange_toInt {x : S32} (h : x ≠ BitVec.intMin 32) : InRange x.toInt := by
  have hb := toInt_bounds x
  have : x.toInt ≠ -2147483648 := fun h' => h ((toInt_eq_intMin_iff x).1 h')
  simp only [InRange, two_pow_31]
  omega

theorem ne_intMin_of_inRange {x : S32} (h : InRange x.toInt) : x ≠ BitVec.intMin 32 := by
  rintro rfl
  simp only [InRange, two_pow_31, toInt_intMin] at h
  omega

theorem litWord_iff (x : S32) : LitWord x = true ↔ LitRange x.toInt := by
  simp only [LitWord, LitRange, Bool.and_eq_true, bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨h0, hm⟩
    exact ⟨fun h => h0 ((toInt_eq_zero_iff x).1 h), inRange_toInt hm⟩
  · rintro ⟨h0, hr⟩
    exact ⟨fun h => h0 ((toInt_eq_zero_iff x).2 h), ne_intMin_of_inRange hr⟩

theorem toInt_encodeLit {l : Int} (h : InRange l) : (encodeLit l).toInt = l := by
  simp only [InRange, two_pow_31] at h
  rw [encodeLit, BitVec.toInt_ofInt]
  exact Int.bmod_eq_of_le_mul_two (by simp; omega) (by simp; omega)

theorem encodeLit_toInt (x : S32) : encodeLit x.toInt = x := BitVec.ofInt_toInt

theorem inRange_zero : InRange 0 := by simp only [InRange, two_pow_31]; omega

theorem litWord_encodeLit {l : Lit} (h : LitRange l) : LitWord (encodeLit l) = true := by
  rw [litWord_iff, toInt_encodeLit h.2]
  exact h

theorem encodeLit_zero : encodeLit 0 = 0 := rfl

/-! ## The nested carrier -/

theorem decodeNested_eq_some {p : Nested} {F : CNF} :
    decodeNested p = some F ↔ p.all (·.all LitWord) = true ∧ F = p.map (·.map BitVec.toInt) := by
  unfold decodeNested
  split
  · next h =>
    constructor
    · intro e
      exact ⟨h, (Option.some.inj e).symm⟩
    · rintro ⟨_, rfl⟩
      rfl
  · next h =>
    constructor
    · intro e
      cases e
    · rintro ⟨h', _⟩
      exact absurd h' h

theorem cnfRange_of_decodeNested {p : Nested} {F : CNF} (h : decodeNested p = some F) :
    CnfRange F := by
  obtain ⟨hw, rfl⟩ := decodeNested_eq_some.1 h
  simp only [List.all_eq_true] at hw
  intro C hC l hl
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hC
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hl
  exact (litWord_iff x).1 (hw c hc x hx)

theorem decodeNested_encode {F : CNF} (h : CnfRange F) :
    decodeNested (encodeNested F) = some F := by
  refine decodeNested_eq_some.2 ⟨?_, ?_⟩
  · simp only [encodeNested, List.all_map, List.all_eq_true, Function.comp_apply]
    intro C hC l hl
    exact litWord_encodeLit (h C hC l hl)
  · simp only [encodeNested, List.map_map, Function.comp_def]
    conv => lhs; rw [← List.map_id F]
    refine List.map_congr_left fun C hC => ?_
    conv => lhs; rw [← List.map_id C]
    exact List.map_congr_left fun l hl => (toInt_encodeLit (h C hC l hl).2).symm

theorem encodeNested_of_decode {p : Nested} {F : CNF} (h : decodeNested p = some F) :
    encodeNested F = p := by
  obtain ⟨_, rfl⟩ := decodeNested_eq_some.1 h
  simp [encodeNested, List.map_map, Function.comp_def, encodeLit_toInt]

theorem decodeNested_none_of_zero {p : Nested} {c : List S32} (hc : c ∈ p) (h0 : (0 : S32) ∈ c) :
    decodeNested p = none := by
  unfold decodeNested
  split
  · next h =>
    simp only [List.all_eq_true] at h
    have := h c hc 0 h0
    simp [LitWord] at this
  · rfl

/-! ## DIMACS streams: what the reader leaves -/

/-- The clauses read and the pending literals make up the whole stream. -/
theorem write_cnf_append_pending (ys : List Int) :
    Dimacs.write (Dimacs.cnf ys) ++ Dimacs.pending ys = ys := by
  induction ys using List.reverseRecOn with
  | nil => rfl
  | append_singleton ys x ih =>
    by_cases hx : x = 0
    · subst hx
      rw [Dimacs.cnf_snoc_zero, Dimacs.pending_snoc_zero]
      have : Dimacs.write (Dimacs.cnf ys ++ [Dimacs.pending ys]) =
          Dimacs.write (Dimacs.cnf ys) ++ (Dimacs.pending ys ++ [0]) := by
        simp [Dimacs.write]
      rw [this, List.append_nil, ← List.append_assoc, ih]
    · rw [Dimacs.cnf_snoc_ne ys hx, Dimacs.pending_snoc_ne ys hx, ← List.append_assoc, ih]

/-- No clause read, and no pending literal, is the terminator `0`. -/
theorem zero_not_mem_read (ys : List Int) :
    (∀ C ∈ Dimacs.cnf ys, (0 : Lit) ∉ C) ∧ (0 : Lit) ∉ Dimacs.pending ys := by
  induction ys using List.reverseRecOn with
  | nil => simp [Dimacs.cnf, Dimacs.pending, Dimacs.read]
  | append_singleton ys x ih =>
    by_cases hx : x = 0
    · subst hx
      rw [Dimacs.cnf_snoc_zero, Dimacs.pending_snoc_zero]
      refine ⟨fun C hC => ?_, by simp⟩
      rcases List.mem_append.1 hC with hC | hC
      · exact ih.1 C hC
      · rw [List.mem_singleton.1 hC]; exact ih.2
    · rw [Dimacs.cnf_snoc_ne ys hx, Dimacs.pending_snoc_ne ys hx]
      refine ⟨ih.1, fun h => ?_⟩
      rcases List.mem_append.1 h with h | h
      · exact ih.2 h
      · exact hx (List.mem_singleton.1 h).symm

theorem pending_eq_nil_iff (ys : List Int) :
    Dimacs.pending ys = [] ↔ ys.getLast?.all (· == 0) = true := by
  induction ys using List.reverseRecOn with
  | nil => simp [Dimacs.pending, Dimacs.read]
  | append_singleton ys x _ =>
    by_cases hx : x = 0
    · subst hx
      simp [Dimacs.pending_snoc_zero]
    · simp [Dimacs.pending_snoc_ne ys hx, hx]

theorem getLast_ok_toInt (xs : List S32) :
    (xs.map BitVec.toInt).getLast?.all (· == 0) = xs.getLast?.all (· == 0) := by
  rw [List.getLast?_map]
  cases xs.getLast? with
  | none => rfl
  | some x =>
    show (x.toInt == 0) = (x == 0)
    by_cases h : x = 0
    · subst h; rfl
    · have : x.toInt ≠ 0 := fun e => h ((toInt_eq_zero_iff x).1 e)
      have e1 : (x.toInt == 0) = false := by simpa using this
      have e2 : (x == 0) = false := by simpa using h
      rw [e1, e2]

/-! ## The stream carrier -/

theorem streamOk_iff (xs : Stream) :
    StreamOk xs = true ↔ (∀ x ∈ xs, x ≠ BitVec.intMin 32) ∧
      Dimacs.pending (xs.map BitVec.toInt) = [] := by
  simp only [StreamOk, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq,
    pending_eq_nil_iff, getLast_ok_toInt]

theorem decodeStream_eq_some {xs : Stream} {F : CNF} :
    decodeStream xs = some F ↔ StreamOk xs = true ∧ F = Dimacs.cnf (xs.map BitVec.toInt) := by
  unfold decodeStream
  split
  · next h =>
    constructor
    · intro e
      exact ⟨h, (Option.some.inj e).symm⟩
    · rintro ⟨_, rfl⟩
      rfl
  · next h =>
    constructor
    · intro e
      cases e
    · rintro ⟨h', _⟩
      exact absurd h' h

theorem write_of_decodeStream {xs : Stream} {F : CNF} (h : decodeStream xs = some F) :
    Dimacs.write F = xs.map BitVec.toInt := by
  obtain ⟨hok, rfl⟩ := decodeStream_eq_some.1 h
  have hp := ((streamOk_iff xs).1 hok).2
  have := write_cnf_append_pending (xs.map BitVec.toInt)
  rwa [hp, List.append_nil] at this

theorem mem_write {F : CNF} {C : Clause} {l : Lit} (hC : C ∈ F) (hl : l ∈ C) : l ∈ Dimacs.write F :=
  List.mem_flatMap.2 ⟨C, hC, List.mem_append_left _ hl⟩

theorem cnfRange_of_decodeStream {xs : Stream} {F : CNF} (h : decodeStream xs = some F) :
    CnfRange F := by
  have hw := write_of_decodeStream h
  obtain ⟨hok, hF⟩ := decodeStream_eq_some.1 h
  have hm := ((streamOk_iff xs).1 hok).1
  intro C hC l hl
  have h0 := (zero_not_mem_read (xs.map BitVec.toInt)).1 C (hF ▸ hC)
  refine ⟨fun h => h0 (h ▸ hl), ?_⟩
  have := mem_write hC hl
  rw [hw, List.mem_map] at this
  obtain ⟨x, hx, rfl⟩ := this
  exact inRange_toInt (hm x hx)

theorem encodeStream_of_decode {xs : Stream} {F : CNF} (h : decodeStream xs = some F) :
    encodeStream F = xs := by
  rw [encodeStream, write_of_decodeStream h, List.map_map]
  simp [Function.comp_def, encodeLit_toInt]

theorem zero_free_of_cnfRange {F : CNF} (h : CnfRange F) : ∀ C ∈ F, (0 : Lit) ∉ C :=
  fun C hC h0 => (h C hC 0 h0).1 rfl

theorem inRange_of_mem_write {F : CNF} (h : CnfRange F) {y : Int} (hy : y ∈ Dimacs.write F) :
    InRange y := by
  obtain ⟨C, hC, hy⟩ := List.mem_flatMap.1 hy
  rcases List.mem_append.1 hy with hy | hy
  · exact (h C hC y hy).2
  · rw [List.mem_singleton.1 hy]; exact inRange_zero

theorem map_toInt_encodeStream {F : CNF} (h : CnfRange F) :
    (encodeStream F).map BitVec.toInt = Dimacs.write F := by
  rw [encodeStream, List.map_map]
  conv => rhs; rw [← List.map_id (Dimacs.write F)]
  exact List.map_congr_left fun y hy => toInt_encodeLit (inRange_of_mem_write h hy)

theorem decodeStream_encode {F : CNF} (h : CnfRange F) :
    decodeStream (encodeStream F) = some F := by
  have hm := map_toInt_encodeStream h
  refine decodeStream_eq_some.2 ⟨(streamOk_iff _).2 ⟨?_, ?_⟩, ?_⟩
  · intro x hx
    apply ne_intMin_of_inRange
    have : x.toInt ∈ Dimacs.write F := hm ▸ List.mem_map_of_mem hx
    exact inRange_of_mem_write h this
  · rw [hm]; exact Dimacs.pending_write (zero_free_of_cnfRange h)
  · rw [hm, Dimacs.cnf_write (zero_free_of_cnfRange h)]

/-! ## Nested and stream readings -/

theorem map_toInt_flatten (p : Nested) :
    (flatten p).map BitVec.toInt = Dimacs.write (p.map (·.map BitVec.toInt)) := by
  simp [flatten, Dimacs.write, List.map_flatMap, List.flatMap_map]

/-- A well-formed nested input is the stream of its clauses, terminated. -/
theorem decodeStream_flatten {p : Nested} {F : CNF} (h : decodeNested p = some F) :
    decodeStream (flatten p) = some F := by
  have hr := cnfRange_of_decodeNested h
  obtain ⟨hw, rfl⟩ := decodeNested_eq_some.1 h
  have hm := map_toInt_flatten p
  refine decodeStream_eq_some.2 ⟨(streamOk_iff _).2 ⟨?_, ?_⟩, ?_⟩
  · intro x hx
    apply ne_intMin_of_inRange
    have : x.toInt ∈ Dimacs.write (p.map (·.map BitVec.toInt)) := hm ▸ List.mem_map_of_mem hx
    exact inRange_of_mem_write hr this
  · rw [hm]; exact Dimacs.pending_write (zero_free_of_cnfRange hr)
  · rw [hm, Dimacs.cnf_write (zero_free_of_cnfRange hr)]

/-- A well-formed stream has a well-formed nested form, of the same formula. -/
theorem decodeNested_of_decodeStream {xs : Stream} {F : CNF} (h : decodeStream xs = some F) :
    decodeNested (encodeNested F) = some F :=
  decodeNested_encode (cnfRange_of_decodeStream h)

/-! ## Problem languages -/

theorem mem_unsatNested {p : Nested} : p ∈ UnsatNested ↔ ∃ F, decodeNested p = some F ∧ F.Unsat :=
  Iff.rfl
theorem mem_satNested {p : Nested} : p ∈ SatNested ↔ ∃ F, decodeNested p = some F ∧ F.Sat :=
  Iff.rfl
theorem mem_unsatStream {xs : Stream} :
    xs ∈ UnsatStream ↔ ∃ F, decodeStream xs = some F ∧ F.Unsat := Iff.rfl
theorem mem_satStream {xs : Stream} : xs ∈ SatStream ↔ ∃ F, decodeStream xs = some F ∧ F.Sat :=
  Iff.rfl

theorem unsatNested_iff_stream (p : Nested) :
    p ∈ UnsatNested ↔ (decodeNested p).isSome ∧ flatten p ∈ UnsatStream := by
  constructor
  · rintro ⟨F, h, hu⟩
    exact ⟨by simp [h], mem_unsatStream.2 ⟨F, decodeStream_flatten h, hu⟩⟩
  · rintro ⟨hs, F, h, hu⟩
    obtain ⟨G, hG⟩ := Option.isSome_iff_exists.1 hs
    have := decodeStream_flatten hG
    rw [h] at this
    cases this
    exact ⟨F, hG, hu⟩

theorem satNested_iff_stream (p : Nested) :
    p ∈ SatNested ↔ (decodeNested p).isSome ∧ flatten p ∈ SatStream := by
  constructor
  · rintro ⟨F, h, hu⟩
    exact ⟨by simp [h], mem_satStream.2 ⟨F, decodeStream_flatten h, hu⟩⟩
  · rintro ⟨hs, F, h, hu⟩
    obtain ⟨G, hG⟩ := Option.isSome_iff_exists.1 hs
    have := decodeStream_flatten hG
    rw [h] at this
    cases this
    exact ⟨F, hG, hu⟩

theorem unsatStream_iff_nested (xs : Stream) :
    xs ∈ UnsatStream ↔ ∃ F, decodeStream xs = some F ∧ encodeNested F ∈ UnsatNested :=
  ⟨fun ⟨F, h, hu⟩ => ⟨F, h, F, decodeNested_of_decodeStream h, hu⟩,
    fun ⟨F, h, G, hG, hu⟩ => by
      rw [decodeNested_of_decodeStream h] at hG
      cases hG
      exact ⟨F, h, hu⟩⟩

theorem satStream_iff_nested (xs : Stream) :
    xs ∈ SatStream ↔ ∃ F, decodeStream xs = some F ∧ encodeNested F ∈ SatNested :=
  ⟨fun ⟨F, h, hu⟩ => ⟨F, h, F, decodeNested_of_decodeStream h, hu⟩,
    fun ⟨F, h, G, hG, hu⟩ => by
      rw [decodeNested_of_decodeStream h] at hG
      cases hG
      exact ⟨F, h, hu⟩⟩

theorem not_satNested_of_unsat {p : Nested} (h : p ∈ UnsatNested) : p ∉ SatNested := by
  obtain ⟨F, hF, hu⟩ := h
  rintro ⟨G, hG, hs⟩
  rw [hF] at hG
  cases hG
  exact CNF.not_sat_of_unsat hu hs

theorem not_satStream_of_unsat {xs : Stream} (h : xs ∈ UnsatStream) : xs ∉ SatStream := by
  obtain ⟨F, hF, hu⟩ := h
  rintro ⟨G, hG, hs⟩
  rw [hF] at hG
  cases hG
  exact CNF.not_sat_of_unsat hu hs

/-! ## Acceptors -/

theorem lratNested_sound : Accepts lratNested ⊆ UnsatNested := by
  rintro p ⟨c, h⟩
  unfold lratNested at h
  split at h
  · next F ss hF _ => exact mem_unsatNested.2 ⟨F, hF, LRAT.check_sound h⟩
  · cases h

theorem lratStream_sound : Accepts lratStream ⊆ UnsatStream := by
  rintro p ⟨c, h⟩
  unfold lratStream at h
  split at h
  · next F ss hF _ => exact mem_unsatStream.2 ⟨F, hF, LRAT.check_sound h⟩
  · cases h

theorem lratNested_iff (p : Nested) (c : List S32) :
    lratNested p c = true ↔
      ∃ F ss, decodeNested p = some F ∧ LratStream.decode c = some ss ∧ LRAT.check F ss = true := by
  unfold lratNested
  split
  · next F ss hF hs => simp [hF, hs]
  · next hne =>
    simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
    intro F ss hF hs _
    exact hne F ss hF hs

theorem lratStream_iff (xs : Stream) (c : List S32) :
    lratStream xs c = true ↔
      ∃ F ss, decodeStream xs = some F ∧ LratStream.decode c = some ss ∧ LRAT.check F ss = true := by
  unfold lratStream
  split
  · next F ss hF hs => simp [hF, hs]
  · next hne =>
    simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
    intro F ss hF hs _
    exact hne F ss hF hs

/-- The model check, unfolded. -/
theorem modelOk_iff (F : CNF) (m : List S32) :
    modelOk F m = true ↔ (∀ x ∈ m, LitWord x = true) ∧
      (∀ l ∈ m.map BitVec.toInt, -l ∉ m.map BitVec.toInt) ∧
      ∀ C ∈ F, ∃ l ∈ C, l ∈ m.map BitVec.toInt := by
  simp only [modelOk, Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
    List.contains_iff_mem, Bool.not_eq_true']
  simp only [List.contains_eq_mem, decide_eq_false_iff_not, and_assoc]

/-- A listed literal is true under the model's assignment. -/
theorem lit_eval_modelAsg {m : List S32} (hc : ∀ l ∈ m.map BitVec.toInt, -l ∉ m.map BitVec.toInt)
    {l : Lit} (hl : l ∈ m.map BitVec.toInt) : Lit.eval (modelAsg m) l = true := by
  simp only [Lit.eval, modelAsg, Lit.var, Lit.pos, beq_iff_eq]
  rcases Int.lt_trichotomy 0 l with h | h | h
  · rw [Int.natAbs_of_nonneg (Int.le_of_lt h)]
    simp [hl, h]
  · subst h
    exact absurd hl (by simpa using hc 0 hl)
  · rw [Int.ofNat_natAbs_of_nonpos (Int.le_of_lt h)]
    have := hc l hl
    simp [this, Int.not_lt.2 (Int.le_of_lt h)]

/-- **A checked model satisfies the formula.** -/
theorem eval_of_modelOk {F : CNF} {m : List S32} (h : modelOk F m = true) :
    F.eval (modelAsg m) = true := by
  obtain ⟨_, hc, hh⟩ := (modelOk_iff F m).1 h
  rw [CNF.eval_eq_true_iff]
  intro C hC
  obtain ⟨l, hl, hm⟩ := hh C hC
  rw [Clause.eval_eq_true_iff]
  exact ⟨l, hl, lit_eval_modelAsg hc hm⟩

theorem satNested_sound : Accepts satNested ⊆ SatNested := by
  rintro p ⟨m, h⟩
  unfold satNested at h
  split at h
  · next F hF => exact mem_satNested.2 ⟨F, hF, _, eval_of_modelOk h⟩
  · cases h

theorem satStream_sound : Accepts satStream ⊆ SatStream := by
  rintro p ⟨m, h⟩
  unfold satStream at h
  split at h
  · next F hF => exact mem_satStream.2 ⟨F, hF, _, eval_of_modelOk h⟩
  · cases h

end Silmaril.Proofs.Logic.SAT.Carrier
