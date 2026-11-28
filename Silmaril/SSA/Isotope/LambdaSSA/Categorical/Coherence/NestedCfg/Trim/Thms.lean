module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Trim.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.CfgReadback.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.Live.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgTrim

/-! # Trim unreferenced labels from an exact CFG witness -/

public section

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgTrim

/-- The selected local label types come directly from the original family.
The outward suffix keeps its types and order. -/
theorem retainLabelRen {τ : Type u} {m n : Nat} (keep : Fin m ↪ Fin n) (S : Fin n → τ) (L : LCtx τ) :
    Ren (List.ofFn (fun i => S (keep i)) ++ L) (List.ofFn S ++ L) (retainLabelIndex keep) :=
  ren keep S L

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  {τ : Type u} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type v} [HasTy Φ τ] [InstructionModel J M Φ]

/-- If the original entry and every original row mention only the retained
labels and ordered outward suffix, restrict the actual graph to those locals.
The syntax certificate gives the reindexed entry and rows. Reindexing a
nested row leaves its internal labels and value binders intact.
Ordinary rolling restricts the outer feedback state. -/
theorem CfgDenotesAt.restrict {k l : Nat} (keep : Fin (k + 1) ↪ Fin (l + 1)) (S : Fin (l + 1) → τ)
    {Γ : VCtx τ} {L : LCtx τ} {entry : Region Φ} {rows : Fin (l + 1) → Region Φ}
    (roll : IterationRolling C) (entryScope : entry.LabelsBound (k + 1 + L.length))
    (rowsScope : ∀ i, (rows i).LabelsBound (k + 1 + L.length))
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)}
    (w : CfgDenotesAt J M S (entry.renameLabels (retainLabelIndex keep))
      (fun i => (rows i).renameLabels (retainLabelIndex keep)) f) :
    CfgDenotesAt J M (fun i => S (keep i)) entry (fun i => rows (keep i)) f :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgTrim.restrict J M keep S roll
    entryScope rowsScope w

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
