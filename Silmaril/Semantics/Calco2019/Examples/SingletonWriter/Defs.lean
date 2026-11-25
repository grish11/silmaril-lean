module

public import Silmaril.Semantics.Calco2019.CompleteElgot.Thms
public import Silmaril.Semantics.ElgotMonads.Thms
public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Logic.Equiv.Option

@[expose] public section

/-! # A writer with a single divergence outcome, CALCO 2019 Example 20(4) -/

universe u

namespace Silmaril.Calco2019.Examples.SingletonWriter

abbrev Model (A : Type u) := WriterT (FreeMonoid A) Part

variable {A X Y : Type u}

/-- The writer extension with a single divergence outcome is Elgot. -/
noncomputable def elgot (A : Type u) : GuardedElgotMonad typeCoproducts.{u} :=
  ofLawfulMonad (Model A)

def result (word : List A) (x : X) : Model A X :=
  WriterT.mk (Part.some (x, FreeMonoid.ofList word))

def divergence : Model A X := WriterT.mk Part.none

/-- The extension carrier is finite output with a result, or the singleton divergence. -/
noncomputable def observe : Model A X ≃ (List A × X) ⊕ PUnit.{u + 1} :=
  let runEquiv : Model A X ≃ Part (X × FreeMonoid A) :=
    ⟨WriterT.run, WriterT.mk, fun _ => rfl, fun _ => rfl⟩
  let reorder := (Equiv.prodCongr (Equiv.refl X) FreeMonoid.toListEquiv).trans (Equiv.prodComm X (List A))
  runEquiv.trans (Part.equivOption.trans (reorder.optionCongr.trans (Equiv.optionEquivSumPUnit _)))

end Silmaril.Calco2019.Examples.SingletonWriter
