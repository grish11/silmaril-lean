module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.WSet.Defs
public import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.WSet

@[expose] public section

/-! # Well-founded trees as small sets in a Grothendieck universe -/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.WSet

open Silmaril.Logic.SetTheory

universe u

/-- Different well-founded trees have different finite-path observation codes. -/
theorem encode_injective {A : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}} :
    Function.Injective (encode (A := A) (B := B)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.encode_injective

/-- Every native W-tree is represented by an element of the carrier set. -/
theorem encode_mem_carrier {A : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}} (t : Tree A B) :
    encode t ∈ carrier A B :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.encode_mem_carrier t

/-- The carrier has exactly the codes of native W-trees. -/
theorem mem_carrier_iff {A z : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}} :
    z ∈ carrier A B ↔ ∃ t : Tree A B, encode t = z :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.mem_carrier_iff

/-- The whole W-type belongs to the same universe as its labels and branch fibres. -/
theorem carrier_mem {U A : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}}
    (hU : IsGrothendieckUniverse U) (hA : A ∈ U) (hB : ∀ a ∈ A, B a ∈ U) :
    carrier A B ∈ U :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.carrier_mem hU hA hB

/-- The carrier depends only on branch fibres at labels belonging to `A`. -/
theorem carrier_congr {A : ZFSet.{u}} {B C : ZFSet.{u} → ZFSet.{u}}
    (h : ∀ a ∈ A, B a = C a) : carrier A B = carrier A C :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.carrier_congr h

/-- Equal labels and equal branch fibres on those labels give equal W carriers. -/
theorem carrier_congr_of_eq {A A' : ZFSet.{u}} {B C : ZFSet.{u} → ZFSet.{u}}
    (hA : A = A') (hB : ∀ a ∈ A, B a = C a) : carrier A B = carrier A' C := by
  subst A'
  exact carrier_congr hB

/-- The encoded carrier is equivalent to the actual W-type, in both directions. -/
noncomputable def equiv (A : ZFSet.{u}) (B : ZFSet.{u} → ZFSet.{u}) :
    Tree A B ≃ carrier A B :=
  Equiv.ofBijective (fun t => ⟨encode t, encode_mem_carrier t⟩) ⟨
    fun _ _ h => encode_injective (congrArg Subtype.val h),
    fun z => by
      obtain ⟨t, ht⟩ := mem_carrier_iff.mp z.property
      exact ⟨t, Subtype.ext ht⟩⟩

@[simp] theorem equiv_apply_val {A : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}}
    (t : Tree A B) : (equiv A B t).val = encode t := rfl

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.WSet

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.WSet

universe u

/-- A nullary constructor is a native tree for the constantly empty branch family. -/
def leaf {A : ZFSet.{u}} (a : A) : Tree A (fun _ => ∅) :=
  .mk a (fun b => False.elim (ZFSet.notMem_empty _ b.property))

/-- The code of a leaf records its label at the empty path. -/
theorem leaf_root {A : ZFSet.{u}} (a : A) :
    ZFSet.pair ∅ a.val ∈ encode (leaf a) :=
  (Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.pair_mem_encode (leaf a) [] a).mpr rfl

/-- Encoded leaves are nonempty observation sets. -/
theorem leaf_encode_ne_empty {A : ZFSet.{u}} (a : A) : encode (leaf a) ≠ ∅ := by
  intro h
  exact ZFSet.notMem_empty _ (h ▸ leaf_root a)

/-- With no labels there are no W-trees, regardless of the branch family. -/
theorem carrier_empty (B : ZFSet.{u} → ZFSet.{u}) : carrier ∅ B = ∅ := by
  apply (ZFSet.eq_empty _).mpr
  intro z hz
  obtain ⟨t, _⟩ := mem_carrier_iff.mp hz
  cases t with
  | mk a _ => exact ZFSet.notMem_empty _ a.property

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.WSet
