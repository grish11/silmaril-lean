module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Apex.Defs

public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Apex

open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.SetTheory
open Silmaril.Logic.TypeTheory.ExtensionalMLTT Silmaril.Logic.TypeTheory.ExtensionalMLTT.Apex

universe u

theorem inclusion_refl (n : ℕ) :
    inclusion.{u} (Nat.le_refl n) = Inst.CoHom.id (finiteBundled.{u} n) := rfl

theorem inclusion_comp {n m k : ℕ} (hnm : n ≤ m) (hmk : m ≤ k) :
    inclusion.{u} (hnm.trans hmk) =
      Inst.CoHom.comp (inclusion hnm) (inclusion hmk) := rfl

theorem toFull_coherent {n m : ℕ} (h : n ≤ m) :
    Inst.CoHom.comp (inclusion.{u} h) (toFull m) = toFull n := rfl

theorem sentence_exhaustive (j : Institution.Sentence.{u}) :
    ∃ n, ∃ jn : Sentence.{u} n, toFullSentence jn = j := by
  refine ⟨j.down.universeBound, ULift.up ⟨j.down, Nat.le_refl _⟩, ?_⟩
  cases j
  rfl

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Apex
