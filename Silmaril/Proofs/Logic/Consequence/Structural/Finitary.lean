module

public import Silmaril.Logic.Consequence.Structural.Finitary.Defs

/-! Proofs for `Silmaril.Logic.Consequence.Structural.Finitary.Thms`. -/

@[expose] public section

namespace Silmaril.Proofs.Logic.Consequence.Structural.Finitary

open Silmaril.Consequence.Structural

universe u

variable {C : Type u}

/-- Choose a premise list for each member of a list of consequences, and cut. -/
theorem cn_cn_subset {R : Rel C} (hc : Cut R) (S : Set C) :
    cn R (cn R S) ⊆ cn R S := by
  rintro c ⟨Γ, hΓ, hd⟩
  choose f hf using hΓ
  let ps : List (List C × C) := Γ.attach.map fun x => (f x.1 x.2, x.1)
  have hsnd : ps.map Prod.snd = Γ := by simp [ps, Function.comp_def]
  have h := @hc ps c (by
    intro p hp
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 hp
    exact (hf x.1 x.2).2) (hsnd ▸ hd)
  refine ⟨_, ?_, h⟩
  intro y hy
  obtain ⟨p, hp, hy⟩ := List.mem_flatMap.1 hy
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 hp
  exact (hf x.1 x.2).1 y hy

theorem onFinset_toFinset [DecidableEq C] {R : Rel C} (hw : WeakSubset R) (Γ : List C) (c : C) :
    onFinset R Γ.toFinset c ↔ R Γ c := by
  constructor
  · exact hw fun x hx => by simpa using hx
  · exact hw fun x hx => by simpa using hx

end Silmaril.Proofs.Logic.Consequence.Structural.Finitary
