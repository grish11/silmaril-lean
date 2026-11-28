module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Paths.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandFamily
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandTyping

/-! # Recover the input type from a finite path of synthesizing jumps -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandBlockParameters

open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical.UnusedSummand.BlockParameters
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical.UnusedSummand (Row)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandTyping (operand_type local_append)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandFamily (row_target_unwidened)

variable {κ : Type u} {Φ : Type v} [HasTy Φ (Ty κ)]
  {n : Nat} {R S : Fin n → Ty κ} {L : LCtx (Ty κ)} {Γ : VCtx (Ty κ)}

theorem type_at_reached (p : Program (Φ := Φ) R L Γ) {K : LCtx (Ty κ)}
    (he : (p.entry.region false id).HasType Γ (List.ofFn S ++ K))
    (hb : ∀ i, (p.blocks i).region.HasType (S i :: Γ) (List.ofFn S ++ K))
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

section Outward

variable {K : LCtx (Ty κ)}

private theorem row_exit {Δ : VCtx (Ty κ)} {ρ : Nat → Nat} (ren : Ren Γ Δ ρ)
    (row : Row (Φ := Φ) R L Γ) {i : Nat} {A : Ty κ} (hit : row.exitsAt i A)
    (typed : (row.region false ρ).HasType Δ (List.ofFn S ++ K)) : At K i A := by
  induction row generalizing Δ ρ with
  | jump j arg => exact hit.elim
  | @exit Γ B j _ arg =>
      obtain ⟨rfl, rfl⟩ := hit
      change (Region.br (n + j) (arg.term.rename ρ)).HasType Δ (List.ofFn S ++ K) at typed
      cases typed with
      | br target argTyped =>
          cases operand_type ren arg _ argTyped
          have bound : (List.ofFn S).length ≤ n + j := by simp
          simpa only [At, List.getElem?_append_right bound, List.length_ofFn, Nat.add_sub_cancel_left]
            using target
  | let₁ value body ih =>
      change (Region.let₁ (value.term.rename ρ) (body.region false (Silmaril.DeBruijn.lift ρ))).HasType
        Δ (List.ofFn S ++ K) at typed
      cases typed with
      | let₁ hv hb =>
          cases operand_type ren value _ hv
          exact ih (ren.lift _) hit hb
  | let₂ value body ih =>
      change (Region.let₂ (value.term.rename ρ) (body.region false (Silmaril.DeBruijn.liftN 2 ρ))).HasType
        Δ (List.ofFn S ++ K) at typed
      cases typed with
      | let₂ hv hb =>
          obtain ⟨rfl, rfl⟩ := Ty.product.inj (operand_type ren value _ hv)
          exact ih ((ren.lift _).lift _) hit hb
  | case arg left right ihl ihr =>
      change (Region.case (arg.term.rename ρ) (left.region false (Silmaril.DeBruijn.lift ρ))
        (right.region false (Silmaril.DeBruijn.lift ρ))).HasType Δ (List.ofFn S ++ K) at typed
      cases typed with
      | case test yes no =>
          obtain ⟨rfl, rfl⟩ := Ty.coprod.inj (operand_type ren arg _ test)
          rcases hit with h | h
          · exact ihl (ren.lift _) h yes
          · exact ihr (ren.lift _) h no

theorem outward_type (p : Program (Φ := Φ) R L Γ) {j : Fin n} {i : Nat} {A : Ty κ}
    (path : p.Reaches j) (hit : (p.blocks j).exitsAt i A) (typed : p.region.HasType Γ K) :
    At K i A := by
  change (Region.cfg (p.entry.region false id) n (fun j => (p.blocks j).region)).HasType Γ K at typed
  cases typed with
  | cfg S he hb =>
      have selected := hb j
      cases block_eq : p.blocks j with
      | parameter row =>
          have aligned := type_at_reached p he hb path
          simp only [block_eq, Block.exitsAt, Block.region, aligned] at hit selected
          exact row_exit (Ren.id (R j :: Γ)) row hit selected
      | captured row =>
          simp only [block_eq, Block.exitsAt, Block.region] at hit selected
          exact row_exit (Ren.wk Γ (S j)) row hit selected

theorem enclosing_type (p : Program (Φ := Φ) R L Γ) {m : Nat} {F : Fin m → Ty κ}
    {j : Fin n} (path : p.Reaches j) (i : Fin m) {A : Ty κ}
    (hit : (p.blocks j).exitsAt i A) (typed : p.region.HasType Γ (List.ofFn F ++ K)) :
    F i = A :=
  Option.some.inj ((local_append F K i).symm.trans (outward_type p path hit typed))

end Outward

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandBlockParameters
