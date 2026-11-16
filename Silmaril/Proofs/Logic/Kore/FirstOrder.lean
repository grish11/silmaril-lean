module

public import Silmaril.Logic.Kore.FirstOrder.Defs

@[expose] public section
namespace Silmaril.Proofs.Logic.Kore.FirstOrder
open CategoryTheory
open Silmaril.Logic
open Silmaril.Logic.Kore.FirstOrder
open Silmaril.Logic.Algebraic.ManySorted (Signature)
variable {S : Type} {A B C : Signature S}

/-- Every source constructor has the same denotation after primitive lowering. -/
theorem denote_lower (M : Matching.FirstOrder.Model A) {k : Nat} {Γ : Fin k → S} {s : S}
    (p : Pattern A Γ s) : ∀ v : (i : Fin k) → M.carrier (Γ i),
      M.denote v p.lower = denote A M v p := by
  classical
  induction p with
  | evar => intro v; rfl
  | app symbol args ih => intro v; simp only [Pattern.lower, Matching.FirstOrder.Model.denote, denote, ih]
  | top => intro v; exact M.denote_top v
  | bottom => intro v; exact M.denote_bottom v
  | not p ih => intro v; exact congrArg (fun x => xᶜ) (ih v)
  | and p q ihp ihq => intro v; exact congrArg₂ Set.inter (ihp v) (ihq v)
  | or p q ihp ihq =>
      intro v; ext result
      simp only [Pattern.lower, Matching.FirstOrder.Model.denote, denote, ihp, ihq,
        Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_union]
      tauto
  | implies p q ihp ihq =>
      intro v; ext result
      simp only [Pattern.lower, Matching.FirstOrder.Model.denote, denote, ihp, ihq,
        Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_ofPred_eq]
      tauto
  | iff p q ihp ihq =>
      intro v; ext result
      simp only [Pattern.lower, Matching.FirstOrder.Model.denote, denote, ihp, ihq,
        Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_ofPred_eq]
      tauto
  | «exists» bound body ih =>
      intro v; simp only [Pattern.lower, Matching.FirstOrder.Model.denote, denote, ih]
  | «forall» bound body ih =>
      intro v; ext result
      simp only [Pattern.lower, Matching.FirstOrder.Model.denote, denote, ih,
        Set.mem_compl_iff, Set.mem_ofPred_eq]
      push Not
      rfl

theorem pattern_map_id {k : Nat} {Γ : Fin k → S} {s : S} (p : Pattern A Γ s) :
    Pattern.map (𝟙 A) p = p := by
  induction p with
  | evar | top | bottom => rfl
  | app symbol args ih => exact congrArg (Pattern.app symbol) (funext ih)
  | not p ih => exact congrArg Pattern.not ih
  | and p q ihp ihq => exact congrArg₂ Pattern.and ihp ihq
  | or p q ihp ihq => exact congrArg₂ Pattern.or ihp ihq
  | implies p q ihp ihq => exact congrArg₂ Pattern.implies ihp ihq
  | iff p q ihp ihq => exact congrArg₂ Pattern.iff ihp ihq
  | «exists» bound body ih => exact congrArg (Pattern.exists bound) ih
  | «forall» bound body ih => exact congrArg (Pattern.forall bound) ih

theorem pattern_map_comp (f : A ⟶ B) (g : B ⟶ C) {k : Nat} {Γ : Fin k → S} {s : S}
    (p : Pattern A Γ s) : Pattern.map (f ≫ g) p = Pattern.map g (Pattern.map f p) := by
  induction p with
  | evar | top | bottom => rfl
  | app symbol args ih => exact congrArg (Pattern.app (g.operations (f.operations symbol))) (funext ih)
  | not p ih => exact congrArg Pattern.not ih
  | and p q ihp ihq => exact congrArg₂ Pattern.and ihp ihq
  | or p q ihp ihq => exact congrArg₂ Pattern.or ihp ihq
  | implies p q ihp ihq => exact congrArg₂ Pattern.implies ihp ihq
  | iff p q ihp ihq => exact congrArg₂ Pattern.iff ihp ihq
  | «exists» bound body ih => exact congrArg (Pattern.exists bound) ih
  | «forall» bound body ih => exact congrArg (Pattern.forall bound) ih

/-- Lowering commutes with the actual many-sorted signature maps. -/
theorem pattern_lower_map (f : A ⟶ B) {k : Nat} {Γ : Fin k → S} {s : S} (p : Pattern A Γ s) :
    (p.map f).lower = Matching.FirstOrder.Pattern.map f p.lower := by
  induction p with
  | evar | top | bottom => rfl
  | app symbol args ih => exact congrArg (Matching.FirstOrder.Pattern.app (f.operations symbol)) (funext ih)
  | not p ih => exact congrArg Matching.FirstOrder.Pattern.neg ih
  | and p q ihp ihq => exact congrArg₂ Matching.FirstOrder.Pattern.conj ihp ihq
  | or p q ihp ihq | implies p q ihp ihq | iff p q ihp ihq =>
      simp only [Pattern.map, Pattern.lower, Matching.FirstOrder.Pattern.map, ihp, ihq]
  | «exists» bound body ih => exact congrArg (Matching.FirstOrder.Pattern.ex bound) ih
  | «forall» bound body ih =>
      simp only [Pattern.map, Pattern.lower, Matching.FirstOrder.Pattern.map, ih]

theorem denote_map (f : A ⟶ B) (M : Matching.FirstOrder.Model B) {k : Nat}
    {Γ : Fin k → S} {s : S} (p : Pattern A Γ s) (v : (i : Fin k) → M.carrier (Γ i)) :
    denote B M v (p.map f) = denote A (Matching.FirstOrder.SignatureMap.reduct f M) v p := by
  revert v
  induction p with
  | evar => intro v; rfl
  | app symbol args ih =>
      intro v; simp only [Pattern.map, denote, ih]; rfl
  | top => intro v; rfl
  | bottom => intro v; rfl
  | not p ih => intro v; exact congrArg (fun x => xᶜ) (ih v)
  | and p q ihp ihq => intro v; exact congrArg₂ Set.inter (ihp v) (ihq v)
  | or p q ihp ihq => intro v; exact congrArg₂ Set.union (ihp v) (ihq v)
  | implies p q ihp ihq =>
      intro v; simp only [Pattern.map, denote, ihp, ihq]; rfl
  | iff p q ihp ihq =>
      intro v; simp only [Pattern.map, denote, ihp, ihq]; rfl
  | «exists» bound body ih =>
      intro v; simp only [Pattern.map, denote, ih]; rfl
  | «forall» bound body ih =>
      intro v; simp only [Pattern.map, denote, ih]; rfl

end Silmaril.Proofs.Logic.Kore.FirstOrder
