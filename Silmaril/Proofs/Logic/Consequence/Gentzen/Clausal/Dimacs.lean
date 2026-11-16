module

public import Silmaril.Logic.Consequence.Gentzen.Clausal.Dimacs.Defs
public import Silmaril.Logic.Consequence.Gentzen.Clausal.Thms
public import Silmaril.Logic.SAT.CNF.Thms
public import Silmaril.Logic.Consequence.Signed.Thms

/-! Proofs for `Silmaril.Logic.Consequence.Gentzen.Clausal.Dimacs.Thms`. -/

@[expose] public section

namespace Silmaril.Proofs.Logic.Consequence.Gentzen.Clausal.Dimacs

open Silmaril.Logic.SAT Silmaril.Consequence Silmaril.Consequence.Gentzen
  Silmaril.Consequence.Gentzen.Clausal

universe u v

theorem cnfSat_litSat_iff {τ : Assignment} {F : Silmaril.Logic.SAT.CNF} :
    CnfSat litSat τ F ↔ F.eval τ = true := by
  rw [CNF.eval_eq_true_iff]
  exact forall₂_congr fun K _ => (Clause.eval_eq_true_iff τ K).symm

theorem cnfUnsat_litSat_iff {F : Silmaril.Logic.SAT.CNF} : CnfUnsat litSat F ↔ F.Unsat := by
  refine forall_congr' fun τ => ?_
  rw [cnfSat_litSat_iff]
  cases F.eval τ <;> simp

variable {A : Type u}

theorem mem_atoms {F : List (List (Signed A))} {K : List (Signed A)} {x : Signed A}
    (hK : K ∈ F) (hx : x ∈ K) : x.atom ∈ atoms F :=
  List.mem_flatMap.2 ⟨K, hK, List.mem_map_of_mem hx⟩

theorem encLit_neg (v : A → Nat) (x : Signed A) : encLit v (-x) = -encLit v x := by
  cases x <;> simp [encLit]

theorem encLit_ne_zero {v : A → Nat} {x : Signed A} (h : v x.atom ≠ 0) : encLit v x ≠ 0 := by
  cases x <;> simpa [encLit, Signed.atom] using h

theorem encode_zero_free {v : A → Nat} {F : List (List (Signed A))} (hc : Coherent v F) :
    ∀ K ∈ encode v F, (0 : Lit) ∉ K := by
  intro K' hK' h0
  obtain ⟨K, hK, rfl⟩ := List.mem_map.1 hK'
  obtain ⟨x, hx, hx0⟩ := List.mem_map.1 h0
  exact encLit_ne_zero (hc.nonzero _ (mem_atoms hK hx)) hx0

open Classical in
/-- A model of the source gives an assignment satisfying the image. -/
theorem sat_encode {M : Type v} {sat : M → Signed A → Prop} (hn : NegSound sat (fun x => -x))
    {v : A → Nat} {F : List (List (Signed A))} (hc : Coherent v F) {m : M}
    (hm : CnfSat sat m F) : (encode v F).Sat := by
  refine ⟨fun n => decide (∃ a ∈ atoms F, v a = n ∧ sat m (.pos a)), ?_⟩
  rw [← cnfSat_litSat_iff]
  intro K' hK'
  obtain ⟨K, hK, rfl⟩ := List.mem_map.1 hK'
  obtain ⟨x, hx, hsx⟩ := hm K hK
  refine ⟨encLit v x, List.mem_map_of_mem hx, ?_⟩
  have ha := mem_atoms hK hx
  cases x with
  | pos a =>
    have h0 : v a ≠ 0 := hc.nonzero a ha
    simp only [litSat, Lit.eval, Lit.var, Lit.pos, encLit, Int.natAbs_natCast]
    simp only [Int.natCast_pos, Nat.pos_of_ne_zero h0, decide_true, beq_true]
    exact decide_eq_true ⟨a, ha, rfl, hsx⟩
  | neg a =>
    have hτ : decide (∃ b ∈ atoms F, v b = v a ∧ sat m (.pos b)) = false := by
      refine decide_eq_false ?_
      rintro ⟨b, hb, hvb, hsb⟩
      have := hc.injOn b hb a ha hvb
      subst this
      exact hn m (.pos b) hsx hsb
    simp only [litSat, Lit.eval, Lit.var, Lit.pos, encLit, Int.natAbs_neg, Int.natAbs_natCast]
    rw [hτ]
    simp

end Silmaril.Proofs.Logic.Consequence.Gentzen.Clausal.Dimacs
