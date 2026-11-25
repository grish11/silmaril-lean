module

public import Silmaril.SSA.RVSDG.Categorical.Defs
public import Silmaril.SSA.RVSDG.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Defs
import Silmaril.Proofs.SSA.RVSDG.Categorical.Agreement
import Silmaril.Proofs.SSA.RVSDG.Categorical.Freyd

/-! # Categorical agreement and the Freyd adapter for acyclic RVSDG -/

public section

namespace Silmaril.SSA.RVSDG

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open scoped MonoidalCategory

universe u v d h w c k
variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {D : Type d} [Category.{h} D] [CartesianMonoidalCategory D]
variable {args outs : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))}

namespace Categorical

/-- Each tagged entry dispatches to its arm with the payload unchanged. -/
theorem dispatch_leg (sel : Selectors D) {n : Nat} {X Y : D}
    (arms : Fin n → (X ⟶ Y)) (i : Fin n) :
    selectorLeg (sel.tag i) ≫ dispatch sel arms = arms i :=
  Proofs.dispatch_leg sel arms i

theorem unpack_pack {F : PortType V S → Type w} {ts : Ports (PortType V S)}
    (input : Tuple F ts) : unpack ts (pack input) = input :=
  Proofs.unpack_pack input

theorem pack_unpack {F : PortType V S → Type w} (ts : Ports (PortType V S))
    (input : portsObj F ts) : pack (unpack ts input) = input :=
  Proofs.pack_unpack ts input

open CategoryTheory.CartesianMonoidalCategory (lift)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (bind)

variable {C : Type c} [Category.{k} C] (J : D ⥤ C)

/-- Pairing with the retained scope is precisely the pure case of the binder
used by the λSSA categorical semantics. -/
theorem freyd_bind_map [SymmetricCategory D] [PremonoidalCategory C]
    [SymmetricPremonoidalCategory C] [FreydCategory J] {R A B : D}
    (f : R ⟶ A) (g : R ⊗ A ⟶ B) :
    bind J (J.map f) (J.map g) = J.map (lift (𝟙 R) f ≫ g) :=
  Proofs.bind_map J f g

/-- The image of γ dispatch is the copair of the mapped arms for the mapped
tagged cocone. The distributive Freyd functor preserves this finite coproduct. -/
theorem freyd_dispatch_map [PreservesFiniteCoproducts J] (sel : Selectors D)
    {n : Nat} {X Y : D} (arms : Fin n → (X ⟶ Y)) :
    (isColimitOfPreserves J (sel.colimit n X)).desc (J.mapCocone (Cofan.mk Y arms)) =
      J.map (dispatch sel arms) :=
  Proofs.dispatch_map J sel arms

end Categorical

/-- The direct graph fold agrees with its inductive linearization at each
numbered prefix, in any admitted Cartesian value model. -/
theorem Graph.denoteOpen_toTerm (m : Categorical.Model Op D) (g : Graph Op args past sigs outs) :
    g.toTerm.denoteOpen m = g.denoteOpen m :=
  Categorical.Proofs.denoteOpen_toTerm m g

theorem Graph.denote_toTerm (m : Categorical.Model Op D) (g : Graph Op args [] sigs outs) :
    g.toTerm.denote m = g.denote m := by
  unfold Term.denote Graph.denote
  rw [Graph.denoteOpen_toTerm]

theorem Term.denote_toGraph (m : Categorical.Model Op D) (t : Term Op args [] sigs outs) :
    t.toGraph.denote m = t.denote m := by
  rw [← Graph.denote_toTerm, Term.toTerm_toGraph]

/-- In the Cartesian category of types the term arrow returns the full
operational output tuple, including any returned snapshot ports. -/
theorem Term.denote_pack (r : Model.{u, v, w} Op) (t : Term Op args [] sigs outs)
    (entry : Tuple r.Val args) :
    t.denote (Categorical.Model.ofRuntime r) (Categorical.pack entry) =
      Categorical.pack (t.run r entry) :=
  Categorical.Proofs.denote_pack r t entry

/-- The same concrete observation for the direct categorical graph fold. -/
theorem Graph.denote_pack (r : Model.{u, v, w} Op) (g : Graph Op args [] sigs outs)
    (entry : Tuple r.Val args) :
    g.denote (Categorical.Model.ofRuntime r) (Categorical.pack entry) =
      Categorical.pack (g.run r entry) := by
  rw [← Graph.denote_toTerm, Term.denote_pack, Graph.run_toTerm]

end Silmaril.SSA.RVSDG
