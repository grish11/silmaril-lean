module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.LabelRenaming.Restriction.Defs

/-! # Recover the written region on a smaller label interface -/

@[expose] public section

universe u

namespace Silmaril.Isotope.LambdaSSA.Region

open Silmaril.DeBruijn

/-- Collect a finite family of checks. Failure of any member rejects the family. -/
def checkFamily {α : Type u} : (n : Nat) → (Fin n → Option α) → Option (Fin n → α)
  | 0, _ => some Fin.elim0
  | n + 1, f => (f 0).bind fun head =>
      (checkFamily n (fun i => f i.succ)).bind fun tail => some (Fin.cases head tail)

/-- Recover a smaller written region under a given label embedding. Each
original transfer must have a preimage in the smaller label prefix.
A nested CFG extends both interfaces by its own local labels. -/
def restrictLabels? {Φ : Type u} (r : Region Φ) (bound : Nat) (ρ : Nat → Nat) : Option (Region Φ) :=
  match r with
  | .br i a =>
      match (List.finRange bound).find? (fun j => ρ j.val == i) with
      | none => none
      | some j => some (.br j.val a)
  | .case a l r =>
      (l.restrictLabels? bound ρ).bind fun l' =>
      (r.restrictLabels? bound ρ).bind fun r' => some (.case a l' r')
  | .let₁ a body => (body.restrictLabels? bound ρ).bind fun b => some (.let₁ a b)
  | .let₂ a body => (body.restrictLabels? bound ρ).bind fun b => some (.let₂ a b)
  | .cfg entry n blocks =>
      (entry.restrictLabels? (n + bound) (liftN n ρ)).bind fun e =>
      (checkFamily n (fun i => (blocks i).restrictLabels? (n + bound) (liftN n ρ))).bind fun bs =>
        some (.cfg e n bs)

end Silmaril.Isotope.LambdaSSA.Region
