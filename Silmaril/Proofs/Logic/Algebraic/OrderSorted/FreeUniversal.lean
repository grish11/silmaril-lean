module

public import Silmaril.Logic.Algebraic.OrderSorted.Free.Defs

public section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Proofs.Logic.Algebraic.OrderSorted.FreeUniversal
open CategoryTheory
open Silmaril.Logic.Algebraic.OrderSorted
open Silmaril.Logic.Algebraic.OrderSorted.Free
variable {A : Signature} {k : ℕ} {Γ : Fin k → A.base.S} {M : Model A}

mutual
/-- Every homomorphism agrees with evaluation on cores once it agrees on variables. -/
theorem onCore (f : model A Γ ⟶ M) (v : ∀ i, M.algebra.carrier (Γ i))
    (hv : ∀ i, f.map (Γ i) (generator i) = v i) {s} (c : Core A Γ s) :
    f.map s (embed c) = evalCore M v c := by
  cases c with
  | var i => exact hv i
  | app o args =>
    change f.map _ ((model A Γ).algebra.op (.base o) args) = _
    rw [f.map_op]
    exact congrArg (M.algebra.op (.base o)) (funext fun i => onNormal f v hv (args i))
/-- Every homomorphism also preserves the root inclusion of a normal term. -/
theorem onNormal (f : model A Γ ⟶ M) (v : ∀ i, M.algebra.carrier (Γ i))
    (hv : ∀ i, f.map (Γ i) (generator i) = v i) {s} (x : Normal A Γ s) :
    f.map s x = eval M v x := by
  cases x with
  | up h c =>
    have hc : Normal.up h c = (model A Γ).algebra.coerce h (embed c) := rfl
    rw [hc, Model.hom_coerce]
    exact congrArg (M.algebra.coerce h) (onCore f v hv c)
end

end Silmaril.Proofs.Logic.Algebraic.OrderSorted.FreeUniversal
