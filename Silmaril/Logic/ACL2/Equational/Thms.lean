module

public import Silmaril.Logic.ACL2.Equational.Defs
import Silmaril.Proofs.Logic.ACL2.Equational

@[expose] public section

namespace Silmaril.Logic.ACL2.Equational

open CategoryTheory Institution Institution.Examples

variable {S T : Signature} {k : Nat}

theorem term_map (σ : S ⟶ T) {ctx : Fin k → (signature S).S}
    {s : (signature S).S} (t : EQ.Term (signature S) ctx s) :
    term (t.map (signatures.map σ)) = (term t).map σ :=
  Proofs.Logic.ACL2.Equational.term_map σ t

theorem term_eval (M : Model S) {ctx : Fin k → (signature S).S} (env : Fin k → M.primitives.Value)
    {s : (signature S).S} (t : EQ.Term (signature S) ctx s) :
    (term t).eval M env = t.eval (algebra M) env :=
  Proofs.Logic.ACL2.Equational.term_eval M env t

theorem holds_iff (M : Model S) (e : EQ.Equation (signature S)) :
    (sentence e).Holds M ↔ e.Holds (algebra M) := by
  rw [sentence, Sentence.holds_eq]
  simp only [term_eval, EQ.Equation.Holds]
  rfl

def corridor (S : Signature) : EQ.room (signature S) ⟶ ACL2.room S :=
  ⟨sentence, Model.functor algebra, holds_iff⟩

theorem sentence_map (σ : S ⟶ T) (e : EQ.Equation (signature S)) :
    sentence (e.map (signatures.map σ)) = (sentence e).map σ := by
  obtain ⟨_, _, _, lhs, rhs⟩ := e
  exact congrArg₂ Sentence.eq (term_map σ lhs) (term_map σ rhs)

theorem corridor_naturality (σ : S ⟶ T) :
    EQ.corridor (signatures.map σ) ≫ corridor T = corridor S ≫ ACL2.corridor σ :=
  Room.hom_ext (funext (sentence_map σ)) (Proofs.Logic.ACL2.Equational.algebra_reduct σ)

/-- Institutional projection to the registered equational institution. At the image signature,
equations translate to ACL2 `equal` statements and ACL2 models give equational algebras. -/
def toEquational : Inst.Hom ACL2.inst EQ.inst where
  Φ := signatures
  η := ⟨corridor, fun _ _ σ => corridor_naturality σ⟩

end Silmaril.Logic.ACL2.Equational
