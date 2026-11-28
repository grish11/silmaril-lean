module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Branch.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Sequence.Model.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Branch.Trace

/-! # Reflection by testing both input tags in the concrete trace algebra -/

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Branch

open Sequence (Normal Sorts signature value run traceAlgebra traceJ validatedTraceModel)
open LambdaSSA.Region (packedExitType)
open LetIter.Semantics.Categorical (boundEnv)

local notation "Γ₀" => (Ctx.nil : Ctx Empty Sorts)

/-- The exact typed program has the predicted effect word and terminal
observation at each input constructor. -/
theorem ProgramBody.run_input (tail : List Sorts) (p : ProgramBody) (tag : value Input) :
    run (p.program tail).toLetCase.2 (boundEnv value (β := inputContext) (PUnit.unit, tag)) =
      (tag.elim (fun _ => p.normal.1) (fun _ => p.normal.2)).observe
        (Sum.inl PUnit.unit : value (packedExitType (Ty.unit :: tail))) :=
  run_program_proof tail p tag

theorem traceSat_iff_normal (tail : List Sorts) (p q : ProgramBody) :
    ((LetCase.inst Γ₀).obj signature).Sat traceAlgebra (grammarCase (equation tail p q)) ↔
      p.normal = q.normal :=
  ⟨traceSat_normal_proof tail p q,
    fun h => Sequence.traceSat_of_repaired _ (repaired_of_normal tail p q h)⟩

theorem repaired_iff_normal (tail : List Sorts) (p q : ProgramBody) :
    Repaired false (equation tail p q) ↔ p.normal = q.normal :=
  ⟨fun h => traceSat_normal_proof tail p q (Sequence.traceSat_of_repaired _ h),
    repaired_of_normal tail p q⟩

theorem traceSat_iff_repaired (tail : List Sorts) (p q : ProgramBody) :
    ((LetCase.inst Γ₀).obj signature).Sat traceAlgebra (grammarCase (equation tail p q)) ↔
      Repaired false (equation tail p q) :=
  (traceSat_iff_normal tail p q).trans (repaired_iff_normal tail p q).symm

/-- The admitted separator tests repaired derivability in the existing room. -/
theorem validatedTrace_sat_iff_repaired (tail : List Sorts) (p q : ProgramBody) :
    (grammarRoom traceJ signature).Sat validatedTraceModel (equation tail p q) ↔
      Repaired false (equation tail p q) :=
  (Sequence.validatedTraceModel_sat_iff _).trans (traceSat_iff_repaired tail p q)

/-- The concrete model reflects room-wide validity on the branch slice. -/
theorem repaired_of_validated_valid (tail : List Sorts) (p q : ProgramBody)
    (valid : ∀ B : (grammarRoom traceJ signature).Mod,
      (grammarRoom traceJ signature).Sat B (equation tail p q)) :
    Repaired false (equation tail p q) :=
  (validatedTrace_sat_iff_repaired tail p q).mp (valid validatedTraceModel)

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Branch
