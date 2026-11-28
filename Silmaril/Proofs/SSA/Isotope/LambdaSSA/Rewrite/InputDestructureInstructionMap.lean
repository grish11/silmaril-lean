module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Input.Destructure.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Flat.InstructionMap.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.InputDestructure

open Silmaril.Isotope.LambdaSSA

universe u v w

variable {Φ : Type u} {Ψ : Type v} (f : Φ → Ψ)

private theorem split_map {τ : Type w} (Γ : VCtx τ) (i : Nat) (r : Region Φ) :
    (Region.InputDestructure.split Γ i r).mapInstr f =
      Region.InputDestructure.split Γ i (r.mapInstr f) := by
  induction Γ generalizing i <;> simp_all [Region.InputDestructure.split, Region.mapInstr, Tm.mapInstr]

theorem packInputsDestructure_map {τ : Type w} (Γ : VCtx τ) (r : Region Φ) :
    (r.packInputsDestructure Γ).mapInstr f = (r.mapInstr f).packInputsDestructure Γ := by
  simp only [Region.packInputsDestructure, split_map, Region.mapInstr_renameVars]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.InputDestructure
