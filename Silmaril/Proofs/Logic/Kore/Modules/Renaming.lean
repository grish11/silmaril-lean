module

public import Silmaril.Logic.Kore.Modules.Checking.Defs

@[expose] public section
namespace Silmaril.Proofs.Logic.Kore.Modules
open Silmaril.Logic.Kore Silmaril.Logic.Kore.Modules.Checking
open Silmaril.Logic.Algebraic.ManySorted (Signature)

private theorem denote_cast {A : Signature String}
    (M : Silmaril.Logic.Matching.FirstOrder.Model A) {k : Nat} {Γ : Fin k → String}
    (v : (i : Fin k) → M.carrier (Γ i)) {s t : String}
    (h : s = t) (p : FirstOrder.Pattern A Γ s) :
    HEq (FirstOrder.denote A M v (h ▸ p)) (FirstOrder.denote A M v p) := by cases h; rfl

private theorem singleton_heq {α β : Type} {x : α} {y : β} (h : HEq x y) :
    HEq ({x} : Set α) ({y} : Set β) := by cases h; rfl

/-- Renaming changes indices, preserving independent KORE denotation under the
corresponding valuations. HEq accommodates the explicit sort equality witnesses. -/
theorem denote_rename {A : Signature String} (M : Silmaril.Logic.Matching.FirstOrder.Model A)
    {k : Nat} {Γ : Fin k → String} {s : String} (p : FirstOrder.Pattern A Γ s) :
    ∀ {l : Nat} {Δ : Fin l → String}
      (f : (i : Fin k) → {j : Fin l // Δ j = Γ i})
      (v : (i : Fin k) → M.carrier (Γ i))
      (w : (i : Fin l) → M.carrier (Δ i)),
      (∀ i, HEq (w (f i).val) (v i)) →
      FirstOrder.denote A M w (rename f p) = FirstOrder.denote A M v p := by
  induction p with
  | evar i =>
      intro l Δ f v w hv
      exact eq_of_heq ((denote_cast M w (f i).property (.evar (f i).val)).trans
        (singleton_heq (hv i)))

  | app sym args ih =>
      intro l Δ f v w hv
      simp only [rename, FirstOrder.denote, fun i => ih i f v w hv]
  | top | bottom => intros; rfl
  | not p ih =>
      intro l Δ f v w hv
      exact congrArg (fun x => xᶜ) (ih f v w hv)
  | and p q ihp ihq =>
      intro l Δ f v w hv
      exact congrArg₂ Set.inter (ihp f v w hv) (ihq f v w hv)
  | or p q ihp ihq =>
      intro l Δ f v w hv
      exact congrArg₂ Set.union (ihp f v w hv) (ihq f v w hv)
  | implies p q ihp ihq =>
      intro l Δ f v w hv
      simp only [rename, FirstOrder.denote, ihp f v w hv, ihq f v w hv]
  | iff p q ihp ihq =>
      intro l Δ f v w hv
      simp only [rename, FirstOrder.denote, ihp f v w hv, ihq f v w hv]
  | «exists» b p ih =>
      intro l Δ f v w hv
      have h (x : M.carrier b) := ih (l := l + 1) (Δ := Fin.cases b Δ) (Fin.cases ⟨0, rfl⟩
        (fun i => ⟨(f i).val.succ, (f i).property⟩)) (Fin.cases x v) (Fin.cases x w)
        (by intro i; refine Fin.cases ?_ (fun j => ?_) i
            · rfl
            · exact hv j)
      simp only [rename, FirstOrder.denote, h]
  | «forall» b p ih =>
      intro l Δ f v w hv
      have h (x : M.carrier b) := ih (l := l + 1) (Δ := Fin.cases b Δ) (Fin.cases ⟨0, rfl⟩
        (fun i => ⟨(f i).val.succ, (f i).property⟩)) (Fin.cases x v) (Fin.cases x w)
        (by intro i; refine Fin.cases ?_ (fun j => ?_) i
            · rfl
            · exact hv j)
      simp only [rename, FirstOrder.denote, h]
end Silmaril.Proofs.Logic.Kore.Modules
