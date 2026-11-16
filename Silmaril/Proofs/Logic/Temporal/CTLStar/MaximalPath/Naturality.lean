module

public import Silmaril.Proofs.Logic.Temporal.CTLStar.MaximalPath.Language

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Temporal.CTLStar.MaximalPath
open CategoryTheory

/-- Actual syntax naturality under arbitrary atom and action renaming. -/
theorem formula_map {S T : ModalMu.Signature} (f : S ⟶ T) (p : NNF.Formula S.Atom)
    (a : S.Action) : (formula p a).map f = formula (p.map f.atom) (f.action a) := by
  simp only [formula, ModalMu.Formula.map, FiniteScalar.formula_map, InfiniteBridge.formula_map]

/-- Relabelled-word acceptance, including maps that identify distinct atoms. -/
theorem accepts_map {A B W : Type} (f : A → B) (p : NNF.Formula A)
    (R : W → W → Prop) (label : W → B → Prop) (w : W) :
    AcceptsPath (p.map f) R label w ↔ AcceptsPath p R (fun v a => label v (f a)) w := by
  rw [accepts_iff, accepts_iff]
  exact exists_congr fun path => and_congr_right fun _ =>
    NNF.Formula.holds_map f path.last (fun t => label (path.state t)) p 0

end Silmaril.Logic.Temporal.CTLStar.MaximalPath
