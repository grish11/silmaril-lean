module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Exits.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Model.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Exits.Packing

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Exits

open Kleisli (value)
open LambdaSSA (At)
open LambdaSSA.Region (packedExitType)
open LambdaSSA.Semantics.Categorical (labelAt_get)
open LetIter.Semantics.Categorical (boundEnv)
open Silmaril.Semantics.NondeterministicTrace (Tagged)

set_option backward.isDefEq.respectTransparency false

local notation "Γ₀" => (Ctx.nil : Ctx Empty Sorts)

theorem repaired_of_normal_proof (H : Sorts) (L : List Sorts)
    (p q : Tree (Exit (H :: L))) (h : p.normal = q.normal) :
    Repaired false (equation H L p q) := by
  have left := p.normalize_operandWith (exitOperand (H :: L)) .nil
  rw [h] at left
  exact .let₁ (left.trans (q.normalize_operandWith (exitOperand (H :: L)) .nil).symm)
    (.equiv (.refl ((program H L p).body.render .base).encode.toLetCase.2.toHasType))

private theorem normalize_program (H : Sorts) (L : List Sorts) (p : Tree (Exit (H :: L))) :
    Repaired false (equation H L p p.normal.render) :=
  .let₁ (p.normalize_operandWith (exitOperand (H :: L)) .nil)
    (.equiv (.refl ((program H L p).body.render .base).encode.toLetCase.2.toHasType))

set_option maxHeartbeats 600000 in
private theorem packed_normal_run (H : Sorts) (L : List Sorts) (p : Normal (Exit (H :: L))) :
    programOutcomes H L p.render = p.outcomesWith Exit.packed := by
  let T := packedExitType (H :: L)
  let ρ := boundEnv value (β := .nil) PUnit.unit
  let body := ((program H L p.render).body.render .base).encode.toLetCase.2
  let finish (x : value T) := Kleisli.run model body (ρ.snoc (A := T) x)
  change (Kleisli.run model (p.render.operandWith (exitOperand (H :: L)) .nil).2 ρ >>=
    finish).outcomes = _
  apply Normal.run_with (success := Exit.packed)
  intro n β ρ' x
  rw [exitOperand_run_proof, pure_bind]
  have runs := router_run_proof model (rfl : At (H :: L) 0 H) (H :: L) (LambdaSSA.Ren.id (H :: L))
    .base ρ x.1 (labelAt_get (H :: L) x.1) x.2
  change finish x.packed = pure x.packed at runs
  rw [runs]
  rfl

theorem programOutcomes_eq_of_sat_proof (H : Sorts) (L : List Sorts) (p q : Tree (Exit (H :: L)))
    (h : ((LetCase.inst Γ₀).obj signature).Sat
      (Kleisli.algebra model) (grammarCase (equation H L p q))) :
    programOutcomes H L p = programOutcomes H L q :=
  congrArg Tagged.outcomes (Kleisli.run_eq_of_sat model (equation H L p q) h PUnit.unit)

theorem programOutcomes_proof (H : Sorts) (L : List Sorts) (p : Tree (Exit (H :: L))) :
    programOutcomes H L p = p.normal.outcomesWith Exit.packed :=
  (programOutcomes_eq_of_sat_proof H L p p.normal.render
    (Kleisli.sat_of_repaired model model_respectsPure _ (normalize_program H L p))).trans
    (packed_normal_run H L p.normal)

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Exits
