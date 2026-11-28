module

public import Silmaril.ProofFormats.LeanNDJSON.MLTT.Defs
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Institution.Defs
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite.Soundness.Thms
import Silmaril.Proofs.ProofFormats.LeanNDJSON.MLTT.Institution

public section

namespace Silmaril.ProofFormats.LeanNDJSON.MLTT

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.TypeTheory.ExtensionalMLTT

universe u

variable {Name : Type} {S T : Signature Name}

/-- Syntactic validity is exactly the source typing judgment in scope. -/
theorem Sentence.valid_iff (s : Sentence S) :
    s.Valid ↔ s.judgment.Γ.JEq s.judgment.A s.judgment.a s.judgment.b := by
  simpa only [Sentence.Valid, Derives, Set.image_empty] using ECtx.JEqH.empty_iff

/-- Consequence is exactly that of the existing fixed-language MLTT logic on
the translated premises and conclusion. -/
theorem derives_iff_mltt (H : Set (Sentence S)) (s : Sentence S) :
    Derives H s ↔ Institution.logic.{0}.Derives (Discrete.mk ())
      ((fun q : Sentence S => ULift.up q.judgment) '' H) (ULift.up s.judgment) :=
  Silmaril.Proofs.ProofFormats.LeanNDJSON.MLTT.derives_iff_mltt H s

/-- Satisfaction is invariant under reduct and sentence translation. -/
theorem budget_satisfaction (f : S ⟶ T) (M : (budgetRoom.{u} T).Mod) (s : Sentence S) :
    (budgetRoom T).Sat M ((budgetFunctor Name).map f |>.sen s) ↔
      (budgetRoom S).Sat (((budgetFunctor Name).map f).mod.obj M) s :=
  ((budgetFunctor Name).map f).sat M s

/-- A finite model validates a fitting judgment derived using rules at its
budget, provided it satisfies the event hypotheses. -/
theorem BudgetModel.satisfies_of_bounded_derivation (M : BudgetModel.{u})
    {H : Set (Sentence S)} {s : Sentence S} (fit : s.judgment.UsesBelow M.levels)
    (hH : ∀ q ∈ H, M.Satisfies q)
    (proof : s.judgment.Γ.JEqB M.levels (Sentence.judgment '' H)
      s.judgment.A s.judgment.a s.judgment.b) : M.Satisfies s :=
  ⟨fit, proof.sound (H := Sentence.judgment '' H) M.tower (fun _ ⟨q, hq, eq⟩ => eq ▸ (hH q hq).2)⟩

/-- Every fixed-budget model expands along the comparison to finite MLTT. -/
theorem toFiniteMLTT_modelExpansive (Name : Type) (levels : Nat) :
    (toFiniteMLTT.{u} Name levels).ModelExpansive :=
  fun _ => (show Function.Surjective (id : Discrete (Silmaril.Logic.SetTheory.FiniteTower.{u} levels) → _)
    from Function.surjective_id)

end Silmaril.ProofFormats.LeanNDJSON.MLTT
