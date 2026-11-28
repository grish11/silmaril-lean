module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Denotation.Defs

public section

open Silmaril.Elgot

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.DenotationProofs

universe u v

variable {E : Type → Type} {A : Type u} {B : Type v}

theorem mapResult_leftInverse {f : A → B} {g : B → A} (h : Function.LeftInverse g f)
    (n : Nat) (x : ITree.Approx E A n) :
    mapResult g n (mapResult f n x) = x := by
  induction n with
  | zero => cases x; rfl
  | succ n ih =>
      simp only [mapResult, Part.map_map]
      have mapId : x.map id = x := by
        ext a
        simp [Part.mem_map_iff]
      conv_rhs => rw [← mapId]
      apply congrArg (fun k => Part.map k x)
      funext node
      cases node with
      | ret a => exact congrArg ITree.Visible.ret (h a)
      | vis e k =>
          apply congrArg (ITree.Visible.vis e)
          funext r
          exact ih (k r)

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.DenotationProofs
