module

public import Silmaril.Logic.Consequence.Gentzen.Finitary.Defs
public import Silmaril.Logic.Consequence.Multi.Defs
public import Silmaril.Logic.Consequence.Structural.Finitary.Defs
import Silmaril.Proofs.Logic.Consequence.Gentzen.Finitary

/-!
# Finite sets and sets of premises and alternatives: exact assumptions

* `onFinset_toFinset` (`WeakSubset S`): `onFinset S Γ.toFinset Δ.toFinset ↔ S Γ Δ`.
* `onSet_list` (`WeakSubset S`): on the member sets of lists, `onSet` is `S`.
* `onFinset_iff_onSet` (`WeakSubset S`): finite sets read either way agree.
* `onSet_mono`: monotone in both sets, with no assumption.
* `onSet_single` (`MultiSystem.WeakR S`): one alternative `{c}` is the single-conclusion
  restriction read on sets (`Structural.onSet` of core `MultiSystem.single`).
* `onSet_valid_sound`: the finitary reading of `Valid` implies `InfValid`. The converse is
  compactness of `sat` and is not claimed (`…Finitary.Examples.not_onSet_valid`); for finite sets
  the two agree (`onSet_valid_finset`).
-/

@[expose] public section

namespace Silmaril.Consequence.Gentzen

universe u v

variable {C : Type u} {S : Seq C}

theorem onFinset_toFinset [DecidableEq C] (hw : WeakSubset S) (Γ Δ : List C) :
    onFinset S Γ.toFinset Δ.toFinset ↔ S Γ Δ :=
  ⟨hw (fun x hx => by simpa using hx) (fun x hx => by simpa using hx),
    hw (fun x hx => by simpa using hx) (fun x hx => by simpa using hx)⟩

theorem onSet_list (hw : WeakSubset S) (Γ Δ : List C) :
    onSet S {x | x ∈ Γ} {x | x ∈ Δ} ↔ S Γ Δ :=
  ⟨fun ⟨_, _, h₁, h₂, h⟩ => hw h₁ h₂ h, fun h => ⟨Γ, Δ, fun _ h => h, fun _ h => h, h⟩⟩

theorem onFinset_iff_onSet (hw : WeakSubset S) (s t : Finset C) :
    onFinset S s t ↔ onSet S ↑s ↑t :=
  Proofs.Logic.Consequence.Gentzen.Finitary.onFinset_iff_onSet hw s t

theorem onSet_mono {A A' B B' : Set C} (hA : A ⊆ A') (hB : B ⊆ B') (h : onSet S A B) :
    onSet S A' B' :=
  let ⟨Γ, Δ, h₁, h₂, h⟩ := h
  ⟨Γ, Δ, fun x hx => hA (h₁ x hx), fun x hx => hB (h₂ x hx), h⟩

theorem onSet_single (hw : MultiSystem.WeakR S) (A : Set C) (c : C) :
    onSet S A {c} ↔ Structural.onSet (MultiSystem.single S) A c :=
  Proofs.Logic.Consequence.Gentzen.Finitary.onSet_single hw A c

variable {M : Type v} {sat : M → C → Prop}

theorem onSet_valid_sound {A B : Set C} (h : onSet (Valid sat) A B) : InfValid sat A B :=
  Proofs.Logic.Consequence.Gentzen.Finitary.onSet_valid_sound h

/-- On finite sets, finitary and infinitary validity agree. -/
theorem onSet_valid_finset (s t : Finset C) : onSet (Valid sat) ↑s ↑t ↔ InfValid sat ↑s ↑t :=
  Proofs.Logic.Consequence.Gentzen.Finitary.onSet_valid_finset s t

end Silmaril.Consequence.Gentzen
