module

public import Silmaril.Logic.Consequence.Structural.Finitary.Defs
public import Mathlib.Order.Closure
import Silmaril.Proofs.Logic.Consequence.Structural.Finitary

/-!
# Finite sets and sets of premises: exact structural assumptions

* `onFinset_toFinset` (`WeakSubset R`): `R Γ c ↔ onFinset R Γ.toFinset c`.
* `onSet_list` (`WeakSubset R`): `onSet R {x | x ∈ Γ} c ↔ R Γ c`.
* `cn_mono` (no assumption), `subset_cn` (`Reflexive R`), `cn_cn` (`Cut R`), and
  `cnClosure` (`Reflexive R`, `Cut R`): the Tarski consequence operator on `Set C`.
-/

@[expose] public section

namespace Silmaril.Consequence.Structural

universe u

variable {C : Type u} {R : Rel C}

theorem onFinset_toFinset [DecidableEq C] (hw : WeakSubset R) (Γ : List C) (c : C) :
    onFinset R Γ.toFinset c ↔ R Γ c :=
  Proofs.Logic.Consequence.Structural.Finitary.onFinset_toFinset hw Γ c

theorem onSet_list (hw : WeakSubset R) (Γ : List C) (c : C) :
    onSet R {x | x ∈ Γ} c ↔ R Γ c :=
  ⟨fun ⟨_, hΔ, h⟩ => hw hΔ h, fun h => ⟨Γ, fun _ hx => hx, h⟩⟩

theorem cn_mono {S T : Set C} (h : S ⊆ T) : cn R S ⊆ cn R T :=
  fun _ ⟨Γ, hΓ, hd⟩ => ⟨Γ, fun x hx => h (hΓ x hx), hd⟩

theorem subset_cn (hr : Reflexive R) (S : Set C) : S ⊆ cn R S :=
  fun c hc => ⟨[c], by simpa using hc, hr (List.mem_singleton_self c)⟩

theorem cn_cn (hc : Cut R) (S : Set C) : cn R (cn R S) ⊆ cn R S :=
  Proofs.Logic.Consequence.Structural.Finitary.cn_cn_subset hc S

/-- A reflexive, cut-closed list relation gives a closure operator on sets of premises. -/
def cnClosure (hr : Reflexive R) (hc : Cut R) : ClosureOperator (Set C) :=
  .mk₂ (cn R) (subset_cn hr) fun _ T h => (cn_mono h).trans (cn_cn hc T)

theorem cnClosure_apply (hr : Reflexive R) (hc : Cut R) (S : Set C) :
    cnClosure hr hc S = cn R S := rfl

end Silmaril.Consequence.Structural
