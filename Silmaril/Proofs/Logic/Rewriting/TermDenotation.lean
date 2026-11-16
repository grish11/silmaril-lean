module

public import Silmaril.Logic.Rewriting.Reachability.Defs

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Rewriting
open CategoryTheory Silmaril.Logic.Institution
variable {S : Type} {A B C : Algebraic.ManySorted.Signature S}

theorem denote_term (M : InhabitedModel A) (cfg : S) (d : Bool) {k} {Γ : Fin k → S}
    (v : ∀ i, M.model.algebra.carrier (Γ i)) {s} (t : Algebraic.ManySorted.Term A Γ s) :
    (reachModel M cfg d).denote v
      (Matching.FirstOrder.Pattern.ofTerm (t.map (termEmbedding A cfg))) = {M.model.algebra.eval v t} := by
  induction t with
  | var => rfl
  | app op args ih =>
      show (reachModel M cfg d).denote v
          (.app (.base op) (fun i => Matching.FirstOrder.Pattern.ofTerm
            ((args i).map (termEmbedding A cfg)))) =
          {M.model.algebra.operation op (fun i => M.model.algebra.eval v (args i))}
      have argument_denotation (i) : (reachModel M cfg d).denote v
          (Matching.FirstOrder.Pattern.ofTerm ((args i).map (termEmbedding A cfg))) =
          {M.model.algebra.eval v (args i)} := ih i
      ext result
      change (∃ values, (∀ i, values i ∈ (reachModel M cfg d).denote v
        (Matching.FirstOrder.Pattern.ofTerm ((args i).map (termEmbedding A cfg)))) ∧
        result = M.model.algebra.operation op values) ↔
        result = M.model.algebra.operation op (fun i => M.model.algebra.eval v (args i))
      constructor
      · rintro ⟨values, members, hr⟩
        have hv : values = fun i => M.model.algebra.eval v (args i) := by
          funext i
          have hi : values i ∈ {M.model.algebra.eval v (args i)} := (argument_denotation i) ▸ members i
          exact hi
        simpa only [hv] using hr
      · intro hr
        refine ⟨_, ?_, hr⟩
        intro i
        rw [argument_denotation i]
        rfl

end Silmaril.Logic.Rewriting
