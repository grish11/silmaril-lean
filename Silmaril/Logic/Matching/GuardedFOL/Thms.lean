module

public import Silmaril.Proofs.Logic.Matching.GuardedFOL.Expansion
public import Silmaril.Proofs.Logic.Matching.GuardedFOL.Syntax
public import Silmaril.Logic.Institution.Borrowing

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.GuardedFOL
open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Examples
variable {S T : FOL.Signature}

abbrev sentence (p : FOL.Sentence S) : FirstOrder.Sentence (signature S).symbols :=
  ⟨0, objContext p.ctx, .truth, formula p.formula⟩

theorem sentence_map (f : S ⟶ T) (p : FOL.Sentence S) :
    SortMaps.Hom.sentence (signatureMap f) (sentence p) = sentence (p.map f) := by
  cases p with
  | mk Γ p => exact congrArg (FirstOrder.Sentence.mk (A := (signature T).symbols) 0 _ MatchingSort.truth) (formula_map f p)

theorem sentence_satisfaction (M : Model S) (p : FOL.Sentence S) :
    FirstOrder.Sentence.Satisfies M.base (sentence p) ↔ p.Holds (decode M) := by
  constructor
  · intro h
    obtain ⟨w⟩ := M.base.nonempty .truth
    exact (formula_denote M p.formula (fun i => i.elim0) w).mp (h _ w)
  · intro h v w
    let sourceEmpty : ∀ i, (decode M).carrier (p.ctx i) := fun i => i.elim0
    have hv : v = (fun i => (sourceEmpty i).val) := funext (fun i => i.elim0)
    change w ∈ M.base.denote v (formula p.formula)
    rw [hv]
    exact (formula_denote M p.formula sourceEmpty w).mpr h

def inst : Inst := ⟨FOL.Signature, institution⟩

def folNatural : FOL.institution ⟶ (𝟭 FOL.Signature) ⋙ institution where
  app S := ⟨sentence, decodeFunctor S, sentence_satisfaction⟩
  naturality := by
    intro S T f
    apply Room.hom_ext
    · funext p
      exact (sentence_map f p).symm
    · exact decodeFunctor_naturality f

/-- Full public FOL, with possibly empty source sorts, into the explicitly
constrained native matching target. This is not an unrestricted matching edge. -/
def folToGuardedMatching : Inst.CoHom FOL.inst inst := ⟨𝟭 _, folNatural⟩

/-- Expansion is up to the proved FOL structure isomorphism, not model equality. -/
theorem expanded_satisfaction (M : FOL.Structure S) (p : FOL.Sentence S) :
    FirstOrder.Sentence.Satisfies (expand M).base (sentence p) ↔ p.Holds M :=
  (sentence_satisfaction _ _).trans (sentence_holds_iso (decodeExpansionIso M) p)

theorem fol_sat_iff (p : FOL.Sentence S) :
    (∃ M : FOL.Structure S, p.Holds M) ↔
      ∃ M : Model S, FirstOrder.Sentence.Satisfies M.base (sentence p) := by
  constructor
  · rintro ⟨M, hp⟩
    exact ⟨expand M, (expanded_satisfaction M p).mpr hp⟩
  · rintro ⟨M, hp⟩
    exact ⟨decode M, (sentence_satisfaction M p).mp hp⟩

theorem fol_unsat_iff (p : FOL.Sentence S) :
    (¬ ∃ M : FOL.Structure S, p.Holds M) ↔
      ¬ ∃ M : Model S, FirstOrder.Sentence.Satisfies M.base (sentence p) :=
  not_congr (fol_sat_iff p)

theorem fol_entails_iff (H : Set (FOL.Sentence S)) (p : FOL.Sentence S) :
    ((FOL.institution.obj S).Entails H p) ↔
      ((institution.obj S).Entails (sentence '' H) (sentence p)) := by
  constructor
  · intro h M hH
    apply (sentence_satisfaction M p).mpr
    apply h (decode M)
    intro q hq
    exact (sentence_satisfaction M q).mp (hH _ ⟨q, hq, rfl⟩)
  · intro h M hH
    apply (expanded_satisfaction M p).mp
    apply h (expand M)
    rintro q ⟨r, hr, rfl⟩
    exact (expanded_satisfaction M r).mpr (hH r hr)
end Silmaril.Logic.Matching.GuardedFOL
