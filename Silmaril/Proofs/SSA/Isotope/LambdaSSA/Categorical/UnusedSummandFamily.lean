module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.UnusedSummand.Readback.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandTyping

/-! # Recover the common part of each written jump's label type -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandFamily

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical.UnusedSummand
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandTyping

variable {κ : Type u} {Φ : Type v} [HasTy Φ (Ty κ)]
  {n : Nat} {R S : Fin n → Ty κ} {L : LCtx (Ty κ)} {Γ : VCtx (Ty κ)}

private def Compatible (tag : Bool) (common actual : Ty κ) : Prop :=
  match tag with
  | false => actual = common
  | true => ∃ D : Ty κ, actual = Silmaril.coprod common D

private theorem row_target {Δ : VCtx (Ty κ)} {ρ : Nat → Nat} (ren : Ren Γ Δ ρ)
    (r : Row (Φ := Φ) R L Γ) (tag : Bool) {i : Fin n} (hit : r.targets i)
    (typed : (r.region tag ρ).HasType Δ (List.ofFn S ++ L)) :
    Compatible tag (R i) (S i) := by
  induction r generalizing Δ ρ with
  | jump j a =>
      change j = i at hit
      subst i
      cases tag with
      | false =>
          change (Region.br j (a.term.rename ρ)).HasType Δ (List.ofFn S ++ L) at typed
          cases typed with
          | br target ha =>
              exact (Option.some.inj (target.symm.trans (local_append S L j))).symm.trans
                (operand_type ren a _ ha)
      | true =>
          change (Region.br j (.inl (a.term.rename ρ))).HasType Δ (List.ofFn S ++ L) at typed
          cases typed with
          | br target ha =>
              have labelEq := Option.some.inj (target.symm.trans (local_append S L j))
              cases ha with
              | inl payload =>
                  cases operand_type ren a _ payload
                  exact ⟨_, labelEq.symm⟩
  | exit i hitExit a => exact False.elim hit
  | let₁ value body ih =>
      change (Region.let₁ (value.term.rename ρ)
        (body.region tag (Silmaril.DeBruijn.lift ρ))).HasType Δ (List.ofFn S ++ L) at typed
      cases typed with
      | let₁ hv hb =>
          cases operand_type ren value _ hv
          exact ih (ren.lift _) hit hb
  | let₂ value body ih =>
      change (Region.let₂ (value.term.rename ρ)
        (body.region tag (Silmaril.DeBruijn.liftN 2 ρ))).HasType Δ (List.ofFn S ++ L) at typed
      cases typed with
      | let₂ hv hb =>
          obtain ⟨rfl, rfl⟩ := Ty.product.inj (operand_type ren value _ hv)
          exact ih ((ren.lift _).lift _) hit hb
  | case arg left right ihl ihr =>
      change (Region.case (arg.term.rename ρ)
        (left.region tag (Silmaril.DeBruijn.lift ρ))
        (right.region tag (Silmaril.DeBruijn.lift ρ))).HasType Δ (List.ofFn S ++ L) at typed
      cases typed with
      | case test yes no =>
          obtain ⟨rfl, rfl⟩ := Ty.coprod.inj (operand_type ren arg _ test)
          rcases hit with h | h
          · exact ihl (ren.lift _) h yes
          · exact ihr (ren.lift _) h no

theorem row_target_unwidened {Δ : VCtx (Ty κ)} {ρ : Nat → Nat} (ren : Ren Γ Δ ρ)
    (r : Row (Φ := Φ) R L Γ) {i : Fin n} (hit : r.targets i)
    (typed : (r.region false ρ).HasType Δ (List.ofFn S ++ L)) : S i = R i :=
  row_target ren r false hit typed

theorem targets_from_typing (p : Program (Φ := Φ) R L Γ)
    (tag : Bool) (he : (p.entry.region tag id).HasType Γ (List.ofFn S ++ L))
    (hb : ∀ i, ((p.blocks i).region tag Nat.succ).HasType (S i :: Γ) (List.ofFn S ++ L)) :
    ∃ tails : Option (Fin n → Ty κ), tails.isSome = tag ∧
      ∀ i, p.targets i → S i = family R tails i := by
  have label (i : Fin n) (hit : p.targets i) : Compatible tag (R i) (S i) := by
    rcases hit with e | ⟨j, b⟩
    · exact row_target (Ren.id Γ) p.entry tag e he
    · exact row_target (Ren.wk Γ (S j)) (p.blocks j) tag b (hb j)
  cases tag with
  | false => exact ⟨none, rfl, label⟩
  | true =>
      classical
      have typed (i : Fin n) : ∃ D : Ty κ, p.targets i → S i = Silmaril.coprod (R i) D := by
        by_cases hit : p.targets i
        · obtain ⟨D, eq⟩ := label i hit
          exact ⟨D, fun _ => eq⟩
        · exact ⟨Silmaril.unit, fun yes => (hit yes).elim⟩
      choose D shape using typed
      exact ⟨some D, rfl, shape⟩

theorem family_from_typing (p : Program (Φ := Φ) R L Γ) (covers : p.targetsEveryLabel)
    (tag : Bool) (he : (p.entry.region tag id).HasType Γ (List.ofFn S ++ L))
    (hb : ∀ i, ((p.blocks i).region tag Nat.succ).HasType (S i :: Γ) (List.ofFn S ++ L)) :
    ∃ tails : Option (Fin n → Ty κ), tails.isSome = tag ∧ S = family R tails := by
  obtain ⟨tails, tag_eq, shape⟩ := targets_from_typing p tag he hb
  exact ⟨tails, tag_eq, funext (fun i => shape i (covers i))⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandFamily
