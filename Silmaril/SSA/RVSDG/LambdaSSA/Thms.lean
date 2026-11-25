module

public import Silmaril.SSA.RVSDG.LambdaSSA.Categorical.Defs
public import Silmaril.SSA.RVSDG.Categorical.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Soundness

/-! # Checked fibres and categorical soundness for straight-line λSSA ↔ RVSDG -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA (Tm)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical (ctxObj lookup Denotes TypingCoherent denote)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

universe u v d h c k
variable {τ : Type u} {Φ : Type v} [HasTy Φ τ]
variable {root Γ : List τ} {past sigs : List (Ports (Ty τ))} {A : τ}

/-- Construct the numbered graph and its relation witness directly from
an admitted λSSA expression. -/
@[expose] def lowerGraph {t : Tm Φ} (h : SSAForm Γ t A) :
    Σ sigs, Σ g : Graph (Opcode Φ) (inputs Γ) [] sigs [.value A], GraphRelated t g :=
  let ⟨sigs, rv, rel⟩ := lower Scope.initial h
  ⟨sigs, rv.toGraph, by simpa only [GraphRelated, Term.toTerm_toGraph] using rel⟩

variable [TypeFormers τ] {D : Type d} [Category.{h} D] [CartesianMonoidalCategory D]
  [HasFiniteCoproducts D] (M : TypeModel τ D) (sel : Categorical.Selectors D)
  (prim : ∀ f : Φ, M.obj (instrSrc f) ⟶ M.obj (instrTrg f))
  {C : Type c} [Category.{k} C] [SymmetricCategory D]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C] [HasFiniteCoproducts C]
  [DistributiveTensor D] [DistributivePremonoidalCategory C]
  (J : D ⥤ C) [DistributiveFreydCategory J] [InstructionModel J M Φ]

omit [SymmetricCategory D] [DistributiveTensor D] in
/-- The input context map carries each typed projection to its RVSDG port. -/
theorem entryMap_lookup (p : Port Γ A) :
    entryMap M Γ sel prim ≫ lookup M (index p) (index_at p) =
      Categorical.project (valueModel M sel prim) (inputPort p) :=
  Proofs.entry_lookup M sel prim p

/-- Every correspondence witness produces an actual λSSA denotation in the
Freyd semantics. At the open boundary it agrees with the RVSDG value arrow
after comparing the scopes and removing the singleton result's trailing unit. -/
theorem Related.sound
    (agree : ∀ f : Φ, InstructionModel.denote (J := J) (M := M) f = J.map (prim f))
    {s : Scope root past Γ} {t : Tm Φ}
    {rv : Term (Opcode Φ) (inputs root) past sigs [.value A]} (rel : Related s t rv) :
    ∃ f : ctxObj M Γ ⟶ M.obj A, Denotes J M rel.typing (J.map f) ∧
      s.contextMap M sel prim ≫ f = rv.denoteOpen (valueModel M sel prim) ≫ (ρ_ (M.obj A)).hom :=
  Proofs.related_sound M sel prim J agree rel

/-- The same equality in the computation category for the independently
defined direct graph denotation. -/
theorem GraphRelated.sound
    (agree : ∀ f : Φ, InstructionModel.denote (J := J) (M := M) f = J.map (prim f))
    {t : Tm Φ} {g : Graph (Opcode Φ) (inputs Γ) [] sigs [.value A]} (rel : GraphRelated t g) :
    ∃ f : ctxObj M Γ ⟶ M.obj A, Denotes J M rel.typing (J.map f) ∧
      J.map (entryMap M Γ sel prim) ≫ J.map f =
        J.map (g.denote (valueModel M sel prim) ≫ (ρ_ (M.obj A)).hom) :=
  Proofs.graph_sound M sel prim J agree rel

/-- In a coherent model the equation identifies the repository's chosen
λSSA denotation with the graph arrow under the boundary maps. -/
theorem GraphRelated.denote_eq [TypingCoherent (Φ := Φ) J M]
    (agree : ∀ f : Φ, InstructionModel.denote (J := J) (M := M) f = J.map (prim f))
    {t : Tm Φ} {g : Graph (Opcode Φ) (inputs Γ) [] sigs [.value A]} (rel : GraphRelated t g) :
    J.map (entryMap M Γ sel prim) ≫ denote J M rel.typing =
      J.map (g.denote (valueModel M sel prim) ≫ (ρ_ (M.obj A)).hom) := by
  obtain ⟨f, d, h⟩ := rel.sound M sel prim J agree
  rwa [d.eq_denote] at h

end Silmaril.SSA.RVSDG.LambdaSSA
