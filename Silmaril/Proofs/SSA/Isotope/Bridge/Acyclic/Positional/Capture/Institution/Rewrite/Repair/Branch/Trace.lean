module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Branch.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Sequence.Model.Thms

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Branch

open Sequence (Normal Sorts Trace signature value model noFree run traceAlgebra traceSat_run)
open Isotope.Semantics (BoundEnv)
open Isotope.LetCase.LocallyNameless (Derivation)
open LambdaSSA.Region (packedExitType)
open LetIter.Semantics.Categorical (boundEnv)

local notation "Γ₀" => (Ctx.nil : Ctx Empty Sorts)
local notation "U" => (Ty.unit : Sorts)

set_option backward.isDefEq.respectTransparency false

private theorem arm_run (a : Arm) {n : Nat} {β : BoundCtx Sorts n} (ρ : BoundEnv value β) :
    run (a.operand β).2 ρ = a.selected.normal.observe PUnit.unit := by
  cases a with
  | body p => exact p.run_operand ρ
  | known tag l r =>
    cases tag
    · change run (.case (.inl (B := U) .unit) (l.operand (β.snoc U)).2 (r.operand (β.snoc U)).2) ρ = _
      simp only [run, Derivation.denote, pure_bind]
      exact l.run_operand (ρ.snoc (A := U) PUnit.unit)
    · change run (.case (.inr (A := U) .unit) (l.operand (β.snoc U)).2 (r.operand (β.snoc U)).2) ρ = _
      simp only [run, Derivation.denote, pure_bind]
      exact r.run_operand (ρ.snoc (A := U) PUnit.unit)

private theorem packed_arm_run (tail : List Sorts) (a : Arm)
    {n : Nat} {β : BoundCtx Sorts n} (ρ : BoundEnv value β) :
    run (a.packed tail β).2 ρ =
      a.selected.normal.observe (Sum.inl PUnit.unit : value (packedExitType (U :: tail))) := by
  let d := (a.operand β).2
  change (Derivation.denote value model (.let₁ d (.inl (.bv (ι := 0)))) noFree ρ).run.run = _
  simp only [Derivation.denote, pure_bind]
  change (((d.denote value model noFree ρ) >>= fun u =>
    (pure (Sum.inl u) : Trace (PUnit ⊕ value (packedExitType tail)))).run.run) = _
  refine (Sequence.run_tag_unit (B := value (packedExitType tail))
    (show Trace PUnit from d.denote value model noFree ρ)).trans ?_
  change ((fun (result, word) => (result.map Sum.inl, word)) <$> run (a.operand β).2 ρ) = _
  rw [arm_run]
  simp only [Normal.observe, Part.map_eq_map, Part.map_some]
  cases a.selected.normal.2 <;> rfl

theorem run_program_proof (tail : List Sorts) (p : ProgramBody) (tag : value Input) :
    run (p.program tail).toLetCase.2 (boundEnv value (β := inputContext) (PUnit.unit, tag)) =
      (tag.elim (fun _ => p.normal.1) (fun _ => p.normal.2)).observe
        (Sum.inl PUnit.unit : value (packedExitType (U :: tail))) := by
  rw [p.program_rendered tail]
  cases tag with
  | inl u =>
    simp only [ProgramBody.rendered, ProgramBody.normal, run, Derivation.denote, pure_bind]
    exact packed_arm_run tail p.left
      (((boundEnv value (β := inputContext) (PUnit.unit, Sum.inl u)).snoc (A := Input)
        (Sum.inl u)).snoc (A := U) u)
  | inr u =>
    simp only [ProgramBody.rendered, ProgramBody.normal, run, Derivation.denote, pure_bind]
    exact packed_arm_run tail p.right
      (((boundEnv value (β := inputContext) (PUnit.unit, Sum.inr u)).snoc (A := Input)
        (Sum.inr u)).snoc (A := U) u)

theorem traceSat_normal_proof (tail : List Sorts) (p q : ProgramBody)
    (h : ((LetCase.inst Γ₀).obj signature).Sat traceAlgebra (grammarCase (equation tail p q))) :
    p.normal = q.normal := by
  have onTag (tag : value Input) :=
    traceSat_run (equation tail p q) h (PUnit.unit, tag)
  apply Prod.ext
  · exact Normal.observe_injective _
      ((run_program_proof tail p (.inl PUnit.unit)).symm.trans
        ((onTag (.inl PUnit.unit)).trans (run_program_proof tail q (.inl PUnit.unit))))
  · exact Normal.observe_injective _
      ((run_program_proof tail p (.inr PUnit.unit)).symm.trans
        ((onTag (.inr PUnit.unit)).trans (run_program_proof tail q (.inr PUnit.unit))))

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Branch
