module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite.Inclusion.Defs
import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.FiniteInclusion
public import Silmaril.Logic.Institution.Borrowing
public import Silmaril.Logic.Institution.Hets.LogicGraph

@[expose] public section

/-! # The indexed family of finite-universe MLTT institutions

The family is functorial in its universe count. Semantic consequence transports
along each inclusion. Reflecting consequence additionally needs an extension
property for finite models in the chosen Lean set carrier.
-/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite

open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.SetTheory

universe u

@[simp] theorem includeSentence_val {n m : ℕ} (h : n ≤ m) (j : Sentence n) :
    (includeSentence h j).val = j.val := rfl

@[simp] theorem inclusion_refl (n : ℕ) :
    inclusion.{u} (Nat.le_refl n) = Inst.CoHom.id (bundled.{u} n) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Finite.inclusion_refl n

@[simp] theorem inclusion_comp {n m k : ℕ} (hnm : n ≤ m) (hmk : m ≤ k) :
    inclusion.{u} (hnm.trans hmk) =
      Inst.CoHom.comp (inclusion hnm) (inclusion hmk) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Finite.inclusion_comp hnm hmk

/-- The universe count indexes a functor into the category of institutions. -/
def family : ℕ ⥤ CoIns.{0, 0, 0, u + 1, u + 1} where
  obj n := bundled.{u} n
  map h := inclusion (leOfHom h)
  map_id n := inclusion_refl n
  map_comp f g := inclusion_comp (leOfHom f) (leOfHom g)

/-- The finite institutions and their inclusions as a Hets logic graph. -/
def hetsGraph : LogicGraph.{0, 0, 0, 0, 0, u + 1, u + 1} :=
  IndexedCoInst.toLogicGraph family.{u}

/-- Each Hets edge realizes the corresponding universe inclusion. -/
theorem hetsGraph_comor {n m : ℕ} (h : n ≤ m) :
    hetsGraph.{u}.comor (homOfLE h) = inclusion.{u} h := rfl

/-- Exact satisfaction preservation under the finite-universe inclusion. -/
theorem inclusion_satisfaction {n m : ℕ} (h : n ≤ m)
    (T : FiniteTower.{u} m) (j : Sentence n) :
    (includeSentence h j).val.ValidIn T.U ↔ j.val.ValidIn (T.restrict h).U := Iff.rfl

/-- A semantic consequence of `MLTT(n)` remains one in `MLTT(m)`. -/
theorem inclusion_entails {n m : ℕ} (h : n ≤ m)
    {H : Set (Sentence n)} {j : Sentence n} (hj : (room.{u} n).Entails H j) :
    (room.{u} m).Entails (includeSentence h '' H) (includeSentence h j) :=
  (inclusion.{u} h).entails_map (S := Discrete.mk ()) hj

/-- Each tower is its own expansion. -/
theorem modelsExtend_refl (n : ℕ) : ModelsExtend.{u} (Nat.le_refl n) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Finite.modelsExtend_refl n

/-- A supplied larger tower expands every zero-level model observationally. -/
theorem modelsExtend_zero (m : ℕ) [HasFiniteTower.{u} m] :
    ModelsExtend.{u} (Nat.zero_le m) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Finite.modelsExtend_zero m

/-- Expanded models agree on every bounded sentence.

Agreement concerns observable satisfaction, not equality of total lookups:
out-of-range entries of smaller finite towers have no closure requirements.
-/
theorem inclusion_observationalExpansion {n m : ℕ} {h : n ≤ m}
    (hext : ModelsExtend.{u} h) (T : (room.{u} n).Mod) :
    ∃ T' : (room.{u} m).Mod, ∀ j : Sentence n,
      (room m).Sat T' (includeSentence h j) ↔ (room n).Sat T j :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Finite.inclusion_observationalExpansion hext T

/-- Borrow semantic consequence when smaller finite models admit expansions. -/
theorem inclusion_entails_iff {n m : ℕ} (h : n ≤ m)
    (hext : ModelsExtend.{u} h) (H : Set (Sentence n)) (j : Sentence n) :
    (room.{u} n).Entails H j ↔
      (room.{u} m).Entails (includeSentence h '' H) (includeSentence h j) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Finite.inclusion_entails_iff h hext H j

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite
