module

public import Silmaril.Logic.FirstOrderLFP.Boolean.Defs

@[expose] public section
namespace Silmaril.Logic.FirstOrderLFP.Boolean

/-- Complementing both input and output preserves monotonicity. -/
noncomputable def complementOperator {W : Type} (F : Set W →o Set W) : Set W →o Set W where
  toFun X := (F Xᶜ)ᶜ
  monotone' := by
    intro X Y h
    exact Set.compl_subset_compl.mpr (F.monotone (Set.compl_subset_compl.mpr h))

/-- Greatest fixed points are definable by Boolean negation and least fixed
points on arbitrary carriers. No primitive greatest-fixed-point syntax is added. -/
theorem complement_lfp {W : Type} (F : Set W →o Set W) :
    (complementOperator F).lfp = F.gfpᶜ := by
  classical
  apply Set.Subset.antisymm
  · apply (complementOperator F).lfp_le
    change (F (F.gfpᶜ)ᶜ)ᶜ ⊆ F.gfpᶜ
    rw [compl_compl, F.map_gfp]
  · have lower : ((complementOperator F).lfp)ᶜ ⊆ F.gfp := by
      apply F.le_gfp
      have fixed := (complementOperator F).map_lfp
      change (F ((complementOperator F).lfp)ᶜ)ᶜ = (complementOperator F).lfp at fixed
      have eq := congrArg (fun X : Set W => Xᶜ) fixed
      rw [compl_compl] at eq
      exact eq.symm.le
    simpa only [compl_compl] using Set.compl_subset_compl.mpr lower

end Silmaril.Logic.FirstOrderLFP.Boolean
