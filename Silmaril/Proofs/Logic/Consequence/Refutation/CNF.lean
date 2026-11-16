module

public import Silmaril.Logic.Consequence.Refutation.CNF.Defs
import Silmaril.Logic.SAT.CNF.Thms

/-! Proofs for `Silmaril.Logic.Consequence.Refutation.CNF.Thms`. -/

@[expose] public section

namespace Silmaril.Proofs.Logic.Consequence.Refutation.CNF

open Silmaril.Logic.SAT Silmaril.Consequence.Refutation Silmaril.Consequence.Refutation.CNF

theorem lit_eval_neg (τ : Assignment) {l : Lit} (h : l ≠ 0) :
    Lit.eval τ (-l) = !Lit.eval τ l := by
  unfold Lit.eval Lit.var Lit.pos
  rw [Int.natAbs_neg]
  have hd : decide ((0 : Int) < -l) = !decide ((0 : Int) < l) := by
    have h' : (l : Int) ≠ 0 := h
    rcases Int.lt_or_gt_of_ne h' with h | h
    · have h1 : ¬ (0 : Int) < l := Int.not_lt.2 (Int.le_of_lt h)
      simp [h1, h]
    · simp [h, Int.le_of_lt h]
  rw [hd]
  cases τ l.natAbs <;> cases decide ((0 : Int) < l) <;> rfl

theorem toCNF_cneg (C : WClause) : toCNF (cneg C) = C.1.map fun l => [-l] := by
  simp only [toCNF, cneg, List.map_map, Function.comp_def]
  exact List.attach_map_val (f := fun l => [-l])

theorem satAll_iff (τ : Assignment) (Γ : List WClause) :
    SatAll csat τ Γ ↔ (toCNF Γ).eval τ = true := by
  simp [SatAll, csat, toCNF, CNF.eval_eq_true_iff]

theorem satAll_cneg (τ : Assignment) (C : WClause) :
    SatAll csat τ (cneg C) ↔ ∀ l ∈ C.1, Lit.eval τ (-l) = true := by
  rw [satAll_iff, toCNF_cneg]
  simp [CNF.eval_eq_true_iff, Clause.eval_eq_true_iff]

theorem ne_zero_of_mem {C : WClause} {l : Lit} (h : l ∈ C.1) : l ≠ 0 :=
  fun h0 => C.2 (h0 ▸ h)

theorem negSound : NegSound csat cneg := by
  intro τ C hn hc
  obtain ⟨l, hl, he⟩ := (Clause.eval_eq_true_iff τ C.1).1 hc
  have := (satAll_cneg τ C).1 hn l hl
  rw [lit_eval_neg τ (ne_zero_of_mem hl), he] at this
  exact absurd this (by decide)

theorem negComplete : NegComplete csat cneg := by
  intro τ C hc
  refine (satAll_cneg τ C).2 fun l hl => ?_
  have : Lit.eval τ l = false := by
    by_contra h
    exact hc ((Clause.eval_eq_true_iff τ C.1).2 ⟨l, hl, by simpa using h⟩)
  rw [lit_eval_neg τ (ne_zero_of_mem hl), this]; rfl

theorem unsat_iff (Γ : List WClause) : Unsat csat Γ ↔ CNF.Unsat (toCNF Γ) := by
  simp only [Unsat, satAll_iff, CNF.Unsat, Bool.not_eq_true]

/-- The assignment falsifying every literal of a clause without complementary pairs. -/
def falsify (C : Clause) : Assignment := fun v => decide (-(v : Int) ∈ C)

theorem falsify_eval {C : WClause} (ht : ¬ Tauto C.1) {l : Lit} (hl : l ∈ C.1) :
    Lit.eval (falsify C.1) l = false := by
  have hne := ne_zero_of_mem hl
  unfold Lit.eval Lit.var Lit.pos falsify
  rcases Int.lt_or_gt_of_ne hne with h | h
  · have e : -((l.natAbs : Nat) : Int) = l := by omega
    have h1 : ¬ (0 : Int) < l := by omega
    simp [e, hl, h1]
  · have e : ((l.natAbs : Nat) : Int) = l := by omega
    have hn : -l ∉ C.1 := fun hn => ht ⟨l, hl, hn⟩
    simp [e, hn, h]

theorem entails_nil_iff_tauto (C : WClause) : Entails csat [] C ↔ Tauto C.1 := by
  constructor
  · intro h
    by_contra ht
    have := h (falsify C.1) (fun _ hx => absurd hx (List.not_mem_nil))
    obtain ⟨l, hl, he⟩ := (Clause.eval_eq_true_iff _ C.1).1 this
    rw [falsify_eval ht hl] at he
    exact absurd he (by decide)
  · rintro ⟨l, hl, hn⟩ τ _
    refine (Clause.eval_eq_true_iff τ C.1).2 ?_
    cases hv : Lit.eval τ l
    · exact ⟨-l, hn, by rw [lit_eval_neg τ (ne_zero_of_mem hl), hv]; rfl⟩
    · exact ⟨l, hl, hv⟩

end Silmaril.Proofs.Logic.Consequence.Refutation.CNF
