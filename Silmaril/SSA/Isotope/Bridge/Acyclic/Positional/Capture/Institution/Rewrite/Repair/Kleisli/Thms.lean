module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Kleisli.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Kleisli.Agreement
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Kleisli.Coherence

/-! # Coherence and exact evaluation for free-type Kleisli models -/

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli

open Silmaril.Elgot
open Isotope.Semantics (InstructionModel)
open LetIter.Semantics.Categorical (boundEnv boundObj)

local notation "Γ₀" => (Ctx.nil : Ctx Empty (Ty Empty))

variable {m : Type → Type} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
  {P : InstrSig (Ty Empty) Bool} (M : InstructionModel value P.Instr m)

/-- The structural free-type interpretation has unique native region
arrows. The fallback extends primitive evaluation to ill-typed inputs. -/
theorem regionCoherent (pureM : InstructionModel.RespectsPure (ε := Bool) M) (bad : {A : Type} → m A) :
    letI := instructions M
    LambdaSSA.Semantics.Categorical.RegionTypingCoherent (Φ := P.Instr) (J (m := m)) types :=
  regionCoherent_proof M pureM bad

/-- The actual LetCase equation has the same satisfaction after validation. -/
theorem validated_sat_iff
    (coherent : letI := instructions M
      LambdaSSA.Semantics.Categorical.RegionTypingCoherent (Φ := P.Instr) (J (m := m)) types)
    (e : GrammarEquation P) :
    (grammarRoom (J (m := m)) P).Sat (validated M coherent) e ↔
      ((LetCase.inst Γ₀).obj P).Sat (algebra M) (grammarCase e) :=
  Iff.rfl

theorem run_eq_of_sat (e : GrammarEquation P)
    (sat : ((LetCase.inst Γ₀).obj P).Sat (algebra M) (grammarCase e))
    (ρ : boundObj types e.1.bound) :
    run M (grammarCase e).2.1.2 (boundEnv value ρ) =
      run M (grammarCase e).2.2.2 (boundEnv value ρ) :=
  run_eq_of_sat_proof M e sat ρ

theorem sat_of_repaired (pureM : InstructionModel.RespectsPure (ε := Bool) M)
    (e : GrammarEquation P) (h : Repaired false e) :
    ((LetCase.inst Γ₀).obj P).Sat (algebra M) (grammarCase e) :=
  sat_of_repaired_proof M pureM e h

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli
