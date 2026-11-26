module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.UnusedSummand.BlockParameters.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandFamily
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandTyping

/-! # Recover the input type from a finite path of synthesizing jumps -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandBlockParameters

open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical.UnusedSummand.BlockParameters
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandFamily (row_target_unwidened)

variable {κ : Type u} {Φ : Type v} [HasTy Φ (Ty κ)]
  {n : Nat} {R S : Fin n → Ty κ} {L : LCtx (Ty κ)} {Γ : VCtx (Ty κ)}

theorem type_at_reached (p : Program (Φ := Φ) R L Γ)
    (he : (p.entry.region false id).HasType Γ (List.ofFn S ++ L))
    (hb : ∀ i, (p.blocks i).region.HasType (S i :: Γ) (List.ofFn S ++ L))
    {i : Fin n} (path : p.Reaches i) : S i = R i := by
  induction path with
  | entry hit => exact row_target_unwidened (Ren.id Γ) p.entry hit he
  | @next j i _ hit ih =>
      have typed := hb j
      cases block_eq : p.blocks j with
      | parameter row =>
          simp only [block_eq, Block.targets, Block.region] at hit typed
          exact row_target_unwidened (Ren.id (R j :: Γ)) row hit (by simpa only [ih] using typed)
      | captured row =>
          simp only [block_eq, Block.targets, Block.region] at hit typed
          exact row_target_unwidened (Ren.wk Γ (S j)) row hit typed

theorem outward_parameter_type {i : Fin n} {j : Nat} {A : Ty κ} (exit : At L j A)
    (typed : (Region.br (n + j) (.var 0) : Region Φ).HasType (S i :: Γ) (List.ofFn S ++ L)) :
    S i = A := by
  cases typed with
  | br target arg =>
      cases arg with
      | var input =>
          exact (Option.some.inj input).trans
            (Option.some.inj (target.symm.trans (UnusedSummandTyping.exit_append S exit)))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandBlockParameters
