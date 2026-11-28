module

public import Silmaril.Logic.Institution.Generalized.Defs
public import Silmaril.Logic.SAT.Institution.Ordinary.Defs

@[expose] public section

/-! # Generalized institutions of SAT valuation semantics -/

namespace Silmaril.Logic.SAT.Institution

open CategoryTheory Silmaril.Logic.Institution

universe u

/-- Total Boolean evaluation on the ordinary CNF sentence and valuation functors. -/
def totalExact : Generalized.ExactInstitution (Type u) Bool where
  Sen := sentenceFunctor totalInstitution
  Mod := modelFunctor totalInstitution
  eval _ M F := F.eval (Discrete.as M)
  eval_map f M F := Problem.eval_rename f (Discrete.as M) F

/-- Compositional strong Kleene evaluation on partial valuations. -/
def kleeneExact : Generalized.ExactInstitution (Type u) (Option Bool) where
  Sen := totalExact.Sen
  Mod := modelFunctor kleeneTruthInstitution
  eval _ M F := F.evalK3 (Discrete.as M)
  eval_map f M F := Problem.evalK3_rename f (Discrete.as M) F

/-- Compositional FDE evaluation retains the Boolean support and refutation bits. -/
def evidenceExact : Generalized.ExactInstitution (Type u) Evidence where
  Sen := totalExact.Sen
  Mod := modelFunctor evidenceSupportInstitution
  eval _ M F := F.evalEvidence (Discrete.as M)
  eval_map f M F := Problem.evalEvidence_rename f (Discrete.as M) F

/-- Completion evaluation is lax in the shared information order for all atom maps. -/
noncomputable def completionLax : Generalized.LaxInstitution (Type u) Generalized.Evidence where
  Sen := kleeneExact.Sen
  Mod := kleeneExact.Mod
  eval _ M F := Generalized.Evidence.ofThree (F.superEval (Discrete.as M))
  le_eval_map f M F :=
    let h := Problem.superEval_rename_informationLE f (Discrete.as M) F
    ⟨h true, h false⟩

end Silmaril.Logic.SAT.Institution
