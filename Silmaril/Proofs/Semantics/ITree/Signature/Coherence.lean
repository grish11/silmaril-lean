module

public import Silmaril.Semantics.ITree.Signature.Defs

public section

namespace Silmaril.Elgot.ITree.Signature.Proofs

open CategoryTheory

universe u v w

variable {S T : Signature.{u}} {A : Type v} {B : Type w}

theorem truncate_approx (f : S ⟶ T) (a : A → B) (n : Nat)
    (obs : Approx S.Event A (n + 1)) :
    Approx.truncate n (f.approx a (n + 1) obs) = f.approx a n (Approx.truncate n obs) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Approx.truncate, Hom.approx, Part.map_eq_map, Part.map_map]
    apply congrArg (fun g => Part.map g obs)
    funext node
    cases node with
    | ret => rfl
    | vis ev next =>
      simp only [Hom.visible, Function.comp_apply, Visible.map_vis]
      congr 1
      funext r
      exact ih _

end Silmaril.Elgot.ITree.Signature.Proofs
