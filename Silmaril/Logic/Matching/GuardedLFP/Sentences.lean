module

public import Silmaril.Logic.Matching.GuardedLFP.Structure
public import Silmaril.Proofs.Logic.Matching.GuardedLFP.Isomorphism

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.GuardedLFP
open CategoryTheory Silmaril.Logic.Institution.Examples
variable {S : FOL.Signature}

abbrev sentence (p : FirstOrderLFP.Sentence S) : FixedPoint.Sentence (signature S).symbols :=
  ⟨0, 0, setContext p.profiles, objContext p.context, .base .truth, formula p.formula⟩

theorem sentence_satisfaction (M : Model S) (p : FirstOrderLFP.Sentence S) :
    FixedPoint.Sentence.Satisfies M.base (sentence p) ↔ FirstOrderLFP.Sat (decode M) p := by
  have hr : restrictEnv M (P := p.profiles) (fun i => i.elim0) = (fun i => i.elim0) :=
    funext fun i => i.elim0
  constructor
  · intro h
    let w := Classical.choice (M.base.nonempty (.base .truth))
    have ht := formula_denote M p.formula (fun i => i.elim0) (fun i => i.elim0) w
    rw [hr] at ht
    exact ht.mp (h _ _ w)
  · intro h v η w
    have hv : v = (fun i => ((fun j => j.elim0 : FirstOrderLFP.ObjEnv (decode M) p.context) i).val) :=
      funext fun i => i.elim0
    have hη : η = (fun i => i.elim0) := funext fun i => i.elim0
    subst v
    subst η
    have ht := formula_denote M p.formula (fun i => i.elim0) (fun i => i.elim0) w
    rw [hr] at ht
    exact ht.mpr h

theorem sentence_iso {M N : FirstOrderLFP.Model S} (e : M.toStructure ≅ N.toStructure)
    (p : FirstOrderLFP.Sentence S) : FirstOrderLFP.Sat M p ↔ FirstOrderLFP.Sat N p := by
  have h := formula_iso e p.formula (fun i => i.elim0) (fun i => i.elim0)
  have hr : pullRelations e (P := p.profiles) (fun i => i.elim0) = (fun i => i.elim0) :=
    funext fun i => i.elim0
  have hv : envEquiv e p.context (fun i => i.elim0) = (fun i => i.elim0) :=
    funext fun i => i.elim0
  rw [hr, hv] at h
  exact h

def decodeExpansionIso (M : FirstOrderLFP.Model S) :
    (decode (expand M.toStructure)).toStructure ≅ M.toStructure := GuardedFOL.decodeExpansionIso M.toStructure

/-- Open object parameters are transported through the actual carrier equivalence;
recursive relation contexts are closed. -/
theorem expanded_formula_denote (M : FirstOrderLFP.Model S) {k : Nat}
    {P : Fin 0 → Profile S} {Γ : Fin k → S.S} (p : FirstOrderLFP.Formula S P Γ)
    (v : FirstOrderLFP.ObjEnv M Γ) (w : (expand M.toStructure).base.carrier (.base .truth)) :
    w ∈ (formula p).denote (expand M.toStructure).base (fun i => some (v i)) (fun i => i.elim0) ↔
      v ∈ p.denote M (fun i => i.elim0) := by
  let v' : FirstOrderLFP.ObjEnv (decode (expand M.toStructure)) Γ :=
    fun i => (GuardedFOL.activeEquiv M.toStructure (Γ i)).symm (v i)
  have hr : restrictEnv (expand M.toStructure) (P := P) (fun i => i.elim0) = (fun i => i.elim0) :=
    funext fun i => i.elim0
  have h := formula_denote (expand M.toStructure) p v' (fun i => i.elim0) w
  rw [hr] at h
  have hi := formula_iso (decodeExpansionIso M) p v' (fun i => i.elim0)
  have hp : pullRelations (decodeExpansionIso M) (P := P) (fun i => i.elim0) = (fun i => i.elim0) :=
    funext fun i => i.elim0
  have hv : envEquiv (decodeExpansionIso M) Γ v' = v :=
    funext fun i => (GuardedFOL.activeEquiv M.toStructure (Γ i)).apply_symm_apply (v i)
  rw [hp, hv] at hi
  exact h.trans hi

theorem expanded_satisfaction (M : FirstOrderLFP.Model S) (p : FirstOrderLFP.Sentence S) :
    FixedPoint.Sentence.Satisfies (expand M.toStructure).base (sentence p) ↔ FirstOrderLFP.Sat M p :=
  (sentence_satisfaction _ _).trans (sentence_iso (decodeExpansionIso M) p)

theorem lfp_sat_iff (p : FirstOrderLFP.Sentence S) :
    (∃ M : FirstOrderLFP.Model S, FirstOrderLFP.Sat M p) ↔
      ∃ M : Model S, FixedPoint.Sentence.Satisfies M.base (sentence p) := by
  constructor
  · rintro ⟨M, hp⟩
    exact ⟨expand M.toStructure, (expanded_satisfaction M p).mpr hp⟩
  · rintro ⟨M, hp⟩
    exact ⟨decode M, (sentence_satisfaction M p).mp hp⟩

theorem lfp_unsat_iff (p : FirstOrderLFP.Sentence S) :
    (¬ ∃ M : FirstOrderLFP.Model S, FirstOrderLFP.Sat M p) ↔
      ¬ ∃ M : Model S, FixedPoint.Sentence.Satisfies M.base (sentence p) :=
  not_congr (lfp_sat_iff p)
end Silmaril.Logic.Matching.GuardedLFP
