module

public import Silmaril.Wasm.Validation.Generic.SSA.Defs

public section

namespace Silmaril.Proofs.Wasm.Validation.Generic.SSA

open Silmaril.Isotope.LambdaSSA
open Silmaril.Wasm.Generic.SSA

variable {Φ τ σ : Type}

theorem mapSlot (f : τ → σ) {slots : List τ} {index : Nat} {type : τ} (slot : At slots index type) :
    At (slots.map f) index (f type) := by
  unfold At at slot ⊢
  simp only [List.getElem?_map, slot, Option.map_some]

theorem mapArgs {source : Boundary τ} {target : Boundary σ} (f : τ → σ)
    (agrees : ∀ type, target.arg (f type) = source.arg type) (params : List τ) :
    (params.map f).mapM target.arg = params.mapM source.arg := by
  induction params with
  | nil => rfl
  | cons head tail ih => simp [List.mapM_cons, agrees, ih]

variable [TypeFormers τ] [TypeFormers σ] [HasTy Φ τ] [HasTy Φ σ]

theorem mapTm (f : TypeMap Φ τ σ) {context : List τ} {term : Tm Φ} {type : τ}
    (valid : term.HasType context type) : term.HasType (context.map f.run) (f.run type) := by
  induction valid with
  | var found => exact .var (mapSlot f.run found)
  | @op _ _ op _ ih => exact f.mapTrg op ▸ .op (f.mapSrc op ▸ ih)
  | let₁ _ _ arg body => exact .let₁ arg body
  | pair _ _ left right => exact (f.mapProduct _ _).symm ▸ .pair left right
  | unit => exact f.mapUnit.symm ▸ .unit
  | let₂ _ _ pair body => exact .let₂ (f.mapProduct _ _ ▸ pair) body
  | inl _ ih => exact (f.mapSum _ _).symm ▸ .inl ih
  | inr _ ih => exact (f.mapSum _ _).symm ▸ .inr ih
  | case _ _ _ discr left right => exact .case (f.mapSum _ _ ▸ discr) left right
  | abort _ ih => exact .abort (f.mapEmpty ▸ ih)

theorem mapRegion (f : TypeMap Φ τ σ) {values labels : List τ} {region : Region Φ}
    (valid : region.HasType values labels) : region.HasType (values.map f.run) (labels.map f.run) := by
  induction valid with
  | br slot arg => exact .br (mapSlot f.run slot) (mapTm f arg)
  | case discr _ _ left right => exact .case (f.mapSum _ _ ▸ mapTm f discr) left right
  | let₁ arg _ body => exact .let₁ (mapTm f arg) body
  | let₂ pair _ body => exact .let₂ (f.mapProduct _ _ ▸ mapTm f pair) body
  | cfg rows _ _ entry blocks =>
    apply Region.HasType.cfg (f.run ∘ rows)
    · simpa only [List.map_append, List.map_ofFn] using entry
    · intro slot
      simpa only [List.map_cons, List.map_append, List.map_ofFn, Function.comp_apply] using blocks slot

end Silmaril.Proofs.Wasm.Validation.Generic.SSA
