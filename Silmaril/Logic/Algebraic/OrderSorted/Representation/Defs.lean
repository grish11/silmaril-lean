module

public import Silmaril.Logic.Algebraic.OrderSorted.Thms
public import Mathlib.Logic.Equiv.Set

/-! Literal-subset representation for the existing non-overloaded fragment.
The common-upper-bound condition is local: different connected components need
not have any common upper sort. No carrier is required to be inhabited. -/
@[expose] public section
namespace Silmaril.Logic.Algebraic.OrderSorted.Representation
open CategoryTheory Silmaril.Logic.Institution.Examples

/-- Upper cones can be amalgamated. This is the local filtration condition used
in the tagged-value quotient; it does not require global directedness. -/
def LocallyFiltered (A : Signature) : Prop :=
  ∀ (s t u : A.base.S), s ≤ t → s ≤ u → ∃ v, t ≤ v ∧ u ≤ v

/-- A finite undirected chain of comparable sorts. -/
inductive Connected (A : Signature) : A.base.S → A.base.S → Prop
  | refl (s) : Connected A s s
  | step {s t u} : Connected A s t → (t ≤ u ∨ u ≤ t) → Connected A s u

/-- The paper's Definition 2.19: each connected component is upward filtered. -/
def ComponentFiltered (A : Signature) : Prop :=
  ∀ s t, Connected A s t → ∃ u, s ≤ u ∧ t ≤ u

/-- Literal subsets of one ambient type, with actual subset inclusions.
Operations keep their original unique profiles; no overloading law is added. -/
structure LiteralModel (A : Signature) where
  ambient : Type
  carrier : A.base.S → Set ambient
  inclusion : ∀ {s t}, s ≤ t → carrier s ⊆ carrier t
  op : ∀ {n w s}, A.base.Op n w s → (∀ i, carrier (w i)) → carrier s

/-- The compiled many-sorted algebra interprets inclusion by the identity on
ambient values, with a transported membership proof. -/
def LiteralModel.algebra {A : Signature} (L : LiteralModel A) : Algebra A where
  carrier s := L.carrier s
  op o args := match o with
    | .base b => L.op b args
    | .inclusion _ _ h => ⟨(args 0).val, L.inclusion h (args 0).property⟩

/-- Sorted homomorphisms preserve base operations and actual inclusions.
No map on unused ambient values is demanded. -/
instance (A : Signature) : Category (LiteralModel A) where
  Hom L K := EQ.Algebra.Hom L.algebra K.algebra
  id L := 𝟙 L.algebra
  comp f g := ⟨fun s x => g.map s (f.map s x), by
    intro n w s o args
    rw [f.map_op, g.map_op]⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- Values are tagged by their original sort before forming the ambient quotient. -/
abbrev Tagged {A : Signature} (M : Model A) := Σ s, M.algebra.carrier s

/-- Two values meet when their images agree at some common upper sort. -/
def Meets {A : Signature} (M : Model A) (x y : Tagged M) : Prop :=
  ∃ (u : A.base.S) (hx : x.1 ≤ u) (hy : y.1 ≤ u),
    M.algebra.coerce hx x.2 = M.algebra.coerce hy y.2

end Silmaril.Logic.Algebraic.OrderSorted.Representation
