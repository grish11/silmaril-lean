module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.Thms
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Capture.Thms

@[expose] public section

namespace Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible

open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA (FiniteCFG Region)

private theorem exit_value_injective {α : Type*} (i j : Nat) (p q : Value α)
    (equal : Region.packedExitValue i p = Region.packedExitValue j q) : i = j ∧ p = q := by
  induction i generalizing j with
  | zero => cases j <;> simp_all [Region.packedExitValue]
  | succ i ih =>
    cases j with
    | zero => simp [Region.packedExitValue] at equal
    | succ j =>
      have tail : Region.packedExitValue i p = Region.packedExitValue j q := by
        simpa [Region.packedExitValue] using equal
      obtain ⟨rfl, rfl⟩ := ih j tail
      exact ⟨rfl, rfl⟩

theorem packedTreeOutput_injective {α : Type*} : Function.Injective (FiniteCFG.packedTreeOutput (α := α)) := by
  rintro ⟨i, p⟩ ⟨j, q⟩ equal
  obtain ⟨rfl, rfl⟩ := exit_value_injective i j p q (congrArg Prod.snd equal)
  rfl

end Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible
