module

public import Silmaril.Proofs.Logic.Temporal.CTLStar.UniversalPath.Language

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Temporal.CTLStar.UniversalPath
open CategoryTheory

/-- Equality of actual scalar syntax, allowing atom collapse and action maps. -/
theorem formula_map {S T : ModalMu.Signature} (f : S ⟶ T) (p : NNF.Formula S.Atom)
    (a : S.Action) : (allFormula p a).map f = allFormula (p.map f.atom) (f.action a) := by
  unfold allFormula
  rw [← ModalMu.Formula.dual_map, MaximalPath.formula_map, NNF.Formula.dual_map]

/-- Renaming labels preserves the entire universal actual-path language. -/
theorem all_map {A B W : Type} (f : A → B) (p : NNF.Formula A)
    (R : W → W → Prop) (label : W → B → Prop) (w : W) :
    AllPaths (p.map f) R label w ↔ AllPaths p R (fun v a => label v (f a)) w := by
  rw [all_iff, all_iff]
  exact forall_congr' fun path => imp_congr_right fun _ =>
    NNF.Formula.holds_map f path.last (fun t => label (path.state t)) p 0

end Silmaril.Logic.Temporal.CTLStar.UniversalPath
