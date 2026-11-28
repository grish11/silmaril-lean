module

public import Silmaril.Logic.SAT.Institution.Generalized.Defs

@[expose] public section

namespace Silmaril.Logic.SAT.Institution

open CategoryTheory Silmaril.Logic.Institution

universe u
variable {A B : Type u}

theorem totalExact_truth_iff (v : TotalValuation A) (F : Problem A) :
    (totalExact.observe (· = true)).Sat A (Discrete.mk v) F ↔
      (totalInstitution.obj A).Sat (Discrete.mk v) F := Iff.rfl

theorem kleeneExact_truth_iff (v : PartialValuation A) (F : Problem A) :
    (kleeneExact.observe (· = some true)).Sat A (Discrete.mk v) F ↔
      (kleeneTruthInstitution.obj A).Sat (Discrete.mk v) F := Iff.rfl

theorem kleeneExact_refutation_iff (v : PartialValuation A) (F : Problem A) :
    (kleeneExact.observe (· = some false)).Sat A (Discrete.mk v) F ↔
      (kleeneRefutationInstitution.obj A).Sat (Discrete.mk v) F := Iff.rfl

theorem evidenceExact_support_iff (v : EvidenceValuation A) (F : Problem A) :
    (evidenceExact.observe (fun e => e.support = true)).Sat A (Discrete.mk v) F ↔
      (evidenceSupportInstitution.obj A).Sat (Discrete.mk v) F := Iff.rfl

theorem evidenceExact_refutation_iff (v : EvidenceValuation A) (F : Problem A) :
    (evidenceExact.observe (fun e => e.refute = true)).Sat A (Discrete.mk v) F ↔
      (evidenceRefutationInstitution.obj A).Sat (Discrete.mk v) F := Iff.rfl

/-- The three-way SAT result gives exactly the core's two universal completion flags. -/
theorem completionLax_eval_eq_ofCompletions (v : PartialValuation A) (F : Problem A) :
    completionLax.eval A (Discrete.mk v) F =
      Generalized.Evidence.ofCompletions {t | Completes v t} (fun t => F.eval t = true) := by
  apply Generalized.Evidence.ext
  · exact propext (Problem.superEval_eq_some v F true)
  · exact propext ((Problem.superEval_eq_some v F false).trans
      (forall_congr' fun _ => imp_congr_right fun _ => Bool.eq_false_iff))

/-- For a covering map both completion flags are exact, including for all injections. -/
theorem completionLax_eval_map_of_coverage (f : A → B) (v : PartialValuation B)
    (covers : CompletionCovers f v) (F : Problem A) :
    completionLax.eval B (Discrete.mk v) (F.rename f) =
      completionLax.eval A (Discrete.mk (reduct f v)) F :=
  congrArg Generalized.Evidence.ofThree (Problem.superEval_rename_of_coverage f v covers F)

end Silmaril.Logic.SAT.Institution
