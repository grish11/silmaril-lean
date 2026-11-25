module

public import Silmaril.Semantics.RuntimeWires.Sliced.Thms

public section

namespace Silmaril.RuntimeWires.Proofs.Sliced.Regression

open CategoryTheory Silmaril.RuntimeWires.Sliced
open scoped MonoidalCategory

/-! Figure 7's side-by-side boxes, with a two-output box on the left and
a nullary-input box on the right. Both choices of seam have the same
external boundaries and different intermediate frontiers. -/

private abbrev figureSignature : Signature Bool where
  Edge := Bool
  source
    | false => [false]
    | true => []
  target
    | false => [true, true]
    | true => [false]

private def parallel : Sheet figureSignature [false] [true, true, false] :=
  .cons (Row.box (S := figureSignature) false (Row.box (S := figureSignature) true .empty)) (.empty _)

private def leftFirst : Sheet figureSignature [false] [true, true, false] :=
  .cons (Row.box (S := figureSignature) false .empty)
    (.cons (.wire true (.wire true (Row.box (S := figureSignature) true .empty))) (.empty _))

private def rightFirst : Sheet figureSignature [false] [true, true, false] :=
  .cons (.wire false (Row.box (S := figureSignature) true .empty))
    (.cons (Row.box (S := figureSignature) false (.wire false .empty)) (.empty _))

private theorem splitLeft : Sheet.SeamEquivalent parallel leftFirst :=
  .rel _ _ (.split (Row.Split.upper (S := figureSignature) false
    (Row.Split.lower (S := figureSignature) true .empty)) (.empty _))

private theorem splitRight : Sheet.SeamEquivalent parallel rightFirst :=
  .rel _ _ (.split (Row.Split.lower (S := figureSignature) false
    (Row.Split.upper (S := figureSignature) true .empty)) (.empty _))

private theorem exchange : Sheet.SeamEquivalent leftFirst rightFirst :=
  .trans _ _ _ (.symm _ _ splitLeft) splitRight

example : leftFirst.denote (fun _ _ => False) = rightFirst.denote (fun _ _ => False) :=
  Sheet.SeamEquivalent.sound exchange _

/-! Figure 9 cancels a runtime crossing and its inverse. This equality
uses the extra runtime equations. The sheets are distinguished by their
vertex counts under the seam calculus. -/

open Presentation

universe u v

variable {G : EffectfulPolygraph.{u,v}}

private def roundTrip (x : G.Obj) :
    Sheet (signature G) [none, some x] [none, some x] :=
  .cons (Row.box (S := signature G) (Edge.moveRight x) .empty)
    (.cons (Row.box (S := signature G) (Edge.moveLeft x) .empty) (.empty _))

example (x : G.Obj) :
    (roundTrip (G := G) x).denote (Relations G) =
      (Sheet.empty [none, some x]).denote (Relations G) := by
  let A : Runtime G := ⟨[none, some x]⟩
  let B : Runtime G := ⟨[some x, none]⟩
  let f : A ⟶ B := Diagram.Presented.ofTerm (crossRight x)
  let g : B ⟶ A := Diagram.Presented.ofTerm (crossLeft x)
  have hr : (Row.box (S := signature G) (.moveRight x) .empty).denote (Relations G) = f :=
    Quotient.sound (Diagram.Congruence.tensor_unit_right (crossRight x))
  have hl : (Row.box (S := signature G) (.moveLeft x) .empty).denote (Relations G) = g :=
    Quotient.sound (Diagram.Congruence.tensor_unit_right (crossLeft x))
  change _ ≫ _ ≫ 𝟙 A = 𝟙 A
  rw [hr, hl, Category.comp_id]
  exact Quotient.sound (Diagram.Congruence.equation (Relations.cancelRight x))

example (x : G.Obj) :
    ¬ Sheet.SeamEquivalent (roundTrip (G := G) x) (.empty [none, some x]) := by
  intro h
  have hcount : 2 = 0 := Sheet.SeamEquivalent.boxCount_eq h
  exact Nat.noConfusion hcount

end Silmaril.RuntimeWires.Proofs.Sliced.Regression
