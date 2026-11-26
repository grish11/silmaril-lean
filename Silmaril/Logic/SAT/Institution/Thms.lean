module

public import Silmaril.Logic.SAT.Institution.Defs
import Silmaril.Proofs.Logic.SAT.Institution.Evaluation
import Silmaril.Proofs.Logic.SAT.Institution.Completion

@[expose] public section

/-! # Change of signature and completion coverage for SAT valuations -/

namespace Silmaril.Logic.SAT.Institution

universe u v w
variable {A : Type u} {B : Type v}

namespace Evidence

theorem le_conj_iff (e a b : Evidence) :
    e.TruthLE (a.conj b) ↔ e.TruthLE a ∧ e.TruthLE b := by
  simp only [TruthLE, conj, Bool.and_eq_true, Bool.or_eq_true]
  grind

theorem disj_le_iff (a b e : Evidence) :
    (a.disj b).TruthLE e ↔ a.TruthLE e ∧ b.TruthLE e := by
  simp only [TruthLE, disj, Bool.and_eq_true, Bool.or_eq_true]
  grind

end Evidence

namespace Problem

theorem rename_id : rename (id : A → A) = id := Proofs.Logic.SAT.Institution.rename_id

theorem rename_comp {D : Type w} (f : A → B) (g : B → D) :
    rename (g ∘ f) = rename g ∘ rename f := Proofs.Logic.SAT.Institution.rename_comp f g

theorem eval_rename (f : A → B) (v : TotalValuation B) (F : Problem A) :
    (F.rename f).eval v = F.eval (reduct f v) := Proofs.Logic.SAT.Institution.eval_rename f v F

theorem evalK3_rename (f : A → B) (v : PartialValuation B) (F : Problem A) :
    (F.rename f).evalK3 v = F.evalK3 (reduct f v) :=
  Proofs.Logic.SAT.Institution.evalWith_rename _ _ _ _ _ f v F

theorem evalEvidence_rename (f : A → B) (v : EvidenceValuation B) (F : Problem A) :
    (F.rename f).evalEvidence v = F.evalEvidence (reduct f v) :=
  Proofs.Logic.SAT.Institution.evalWith_rename _ _ _ _ _ f v F

/-- The translation preserves the existing Boolean evaluator at every assignment. -/
theorem eval_ofCNF (v : TotalValuation Nat) (F : SAT.CNF) :
    (ofCNF F).eval v = SAT.CNF.eval v F := Proofs.Logic.SAT.Institution.eval_ofCNF v F

theorem evalK3_total (v : TotalValuation A) (F : Problem A) :
    F.evalK3 (some ∘ v) = some (F.eval v) := Proofs.Logic.SAT.Institution.evalK3_total v F

theorem evalEvidence_ofK3 (v : PartialValuation A) (F : Problem A) :
    F.evalEvidence (Evidence.ofK3 ∘ v) = Evidence.ofK3 (F.evalK3 v) :=
  Proofs.Logic.SAT.Institution.evalEvidence_ofK3 v F

theorem evalEvidence_total (v : TotalValuation A) (F : Problem A) :
    F.evalEvidence (Evidence.ofK3 ∘ some ∘ v) = Evidence.ofK3 (some (F.eval v)) := by
  rw [← evalK3_total, ← evalEvidence_ofK3]

theorem evalK3_informationLE {v v' : PartialValuation A}
    (h : ∀ a, K3.InformationLE (v a) (v' a)) (F : Problem A) :
    K3.InformationLE (F.evalK3 v) (F.evalK3 v') :=
  Proofs.Logic.SAT.Institution.evalK3_informationLE h F

theorem evalEvidence_informationLE {v v' : EvidenceValuation A}
    (h : ∀ a, Evidence.InformationLE (v a) (v' a)) (F : Problem A) :
    Evidence.InformationLE (F.evalEvidence v) (F.evalEvidence v') :=
  Proofs.Logic.SAT.Institution.evalEvidence_informationLE h F

end Problem

theorem exists_completion (v : PartialValuation A) : ∃ t, Completes v t :=
  Proofs.Logic.SAT.Institution.exists_completion v

theorem completes_reduct (f : A → B) {v : PartialValuation B} {t : TotalValuation B}
    (h : Completes v t) : Completes (reduct f v) (reduct f t) :=
  Proofs.Logic.SAT.Institution.completes_reduct f h

/-- A completion of the reduct lifts exactly when it is constant on the fibres of `f`. -/
theorem completion_lifts_iff (f : A → B) (v : PartialValuation B) {s : TotalValuation A}
    (hs : Completes (reduct f v) s) :
    (∃ t, Completes v t ∧ reduct f t = s) ↔ ∀ a a', f a = f a' → s a = s a' :=
  Proofs.Logic.SAT.Institution.completion_lifts_iff f v hs

namespace Problem

theorem superEval_eq_some (v : PartialValuation A) (F : Problem A) (b : Bool) :
    F.superEval v = some b ↔ ∀ t, Completes v t → F.eval t = b :=
  Proofs.Logic.SAT.Institution.superEval_eq_some v F b

theorem superEval_eq_none (v : PartialValuation A) (F : Problem A) :
    F.superEval v = none ↔
      (∃ t, Completes v t ∧ F.eval t = true) ∧ (∃ t, Completes v t ∧ F.eval t = false) :=
  Proofs.Logic.SAT.Institution.superEval_eq_none v F

theorem superEval_total (t : TotalValuation A) (F : Problem A) :
    F.superEval (some ∘ t) = some (F.eval t) := Proofs.Logic.SAT.Institution.superEval_total t F

/-- Every compositional strong Kleene verdict survives quantification over total completions. -/
theorem evalK3_informationLE_superEval (v : PartialValuation A) (F : Problem A) :
    K3.InformationLE (F.evalK3 v) (F.superEval v) :=
  Proofs.Logic.SAT.Institution.evalK3_informationLE_superEval v F

theorem superEval_rename_of_injective (f : A → B) (hf : Function.Injective f)
    (v : PartialValuation B) (F : Problem A) :
    (F.rename f).superEval v = F.superEval (reduct f v) :=
  Proofs.Logic.SAT.Institution.superEval_rename_of_injective f hf v F

/-- Identification of atoms can remove completions and make an unknown verdict definite. -/
theorem superEval_rename_informationLE (f : A → B) (v : PartialValuation B) (F : Problem A) :
    K3.InformationLE (F.superEval (reduct f v)) ((F.rename f).superEval v) :=
  Proofs.Logic.SAT.Institution.superEval_rename_informationLE f v F

end Problem

end Silmaril.Logic.SAT.Institution
