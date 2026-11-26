module

public import Silmaril.Logic.ACL2.Equational.Defs

@[expose] public section

namespace Silmaril.Proofs.Logic.ACL2.Equational

open CategoryTheory Silmaril.Logic.ACL2 Silmaril.Logic.ACL2.Equational
open Silmaril.Logic.Institution.Examples

variable {S T : Signature} {k : Nat}

theorem term_map (σ : S ⟶ T) {ctx : Fin k → (signature S).S}
    {s : (signature S).S} (t : EQ.Term (signature S) ctx s) :
    term (t.map (signatures.map σ)) = (term t).map σ := by
  induction t with
  | var => rfl
  | app op _ ih =>
    simp only [term, EQ.Term.map, ih]
    cases op <;> rfl

theorem term_eval (M : Model S) {ctx : Fin k → (signature S).S} (env : Fin k → M.primitives.Value)
    {s : (signature S).S} (t : EQ.Term (signature S) ctx s) :
    (term t).eval M env = t.eval (algebra M) env := by
  induction t with
  | var => rfl
  | app op args ih =>
    have hop : (op.term fun i => term (args i)).eval M env =
        op.eval M (fun i => (term (args i)).eval M env) := by
      cases op <;> rfl
    simp only [term, EQ.Term.eval, algebra, hop, ih]

theorem algebra_reduct (σ : S ⟶ T) :
    Model.functor (algebra (S := T)) ⋙ EQ.Algebra.reduct (signatures.map σ) =
      Model.functor (Model.reduct σ) ⋙ Model.functor (algebra (S := S)) := by
  refine Functor.ext (fun M => ?_) ?_
  · change EQ.Algebra.mk (fun _ => M.primitives.Value) _ = EQ.Algebra.mk (fun _ => M.primitives.Value) _
    congr 1
    funext n _ _ op args
    cases op <;> rfl
  · intro M N h
    rcases h with ⟨⟨⟩⟩
    simp [Model.functor, Functor.comp_map]
    have cancel {X Y : EQ.Algebra (signature S)} (h : X = Y) :
        𝟙 X = eqToHom h ≫ 𝟙 Y ≫ eqToHom h.symm := by
      cases h
      simp
    exact cancel _

end Silmaril.Proofs.Logic.ACL2.Equational
