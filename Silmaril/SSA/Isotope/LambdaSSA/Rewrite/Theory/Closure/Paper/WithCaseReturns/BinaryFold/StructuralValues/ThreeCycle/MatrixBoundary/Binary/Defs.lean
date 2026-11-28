module

public import Silmaril.Semantics.Calco2019.Trace.CounterSemiring.ThreeCycle.Thms
public import Mathlib.Data.Matrix.Mul

/-! # Binary-fold feedback with two retained states -/

@[expose] public section

namespace Silmaril.Calco2019.CounterSemiring.ThreeCycle.Binary

abbrev Bit := Fin 2
abbrev PhaseState := Bit ⊕ Bit
abbrev Weight := Matrix Bit Bit Scalar

/-- Eliminate one feedback state in a network with separate external and
recursive input rows. -/
def eliminate {I X E : Type} (s : X) (f : (I ⊕ X) → (E ⊕ X) → Scalar) :
    (I ⊕ X) → (E ⊕ X) → Scalar :=
  fun i j => f i j + f i (.inr s) * Scalar.star (f (.inr s) (.inr s)) * f (.inr s) j

/-- Copy the step into the external and recursive input rows of the network. -/
def network {X E : Type} (r : Matrix X X Scalar) (e : Matrix X E Scalar) :
    (X ⊕ X) → (E ⊕ X) → Scalar :=
  fun i j => Sum.elim (e (i.elim id id)) (r (i.elim id id)) j

/-- Tail-first elimination of a retained Bit. -/
def feedback {E : Type} (r : Weight) (e : Matrix Bit E Scalar) : Matrix Bit E Scalar :=
  Matrix.of fun i j => eliminate 0 (eliminate 1 (network r e)) (.inl i) (.inl j)

/-- Advance to the other phase on recurrence, retaining the actual Bit. -/
def alternating (r : Weight) : Matrix PhaseState PhaseState Scalar :=
  Matrix.of fun
  | .inl _, .inl _ | .inr _, .inr _ => 0
  | .inl i, .inr j | .inr i, .inl j => r i j

/-- Copy the exit row on both phases. -/
def duplicate {E : Type} (e : Matrix Bit E Scalar) : Matrix PhaseState E Scalar :=
  Matrix.of fun i j => e (i.elim id id) j

/-- The function matrix of the pure fold, whose two arms forward the Bit. -/
def foldMatrix : Matrix PhaseState Bit Scalar :=
  Matrix.of fun i j => if i.elim id id = j then 1 else 0

/-- The same tail-first matrix elimination on the two copies of Bit. -/
def phaseFeedback {E : Type} (r : Weight) (e : Matrix Bit E Scalar) : Matrix PhaseState E Scalar :=
  let f := network (alternating r) (duplicate e)
  let reduced := eliminate (.inl 0) (eliminate (.inl 1) (eliminate (.inr 0) (eliminate (.inr 1) f)))
  Matrix.of fun i j => reduced (.inl i) (.inl j)

/-- A two-by-two matrix in row order. -/
def entries (a b c d : Scalar) : Weight :=
  Matrix.of fun i j => if i = 0 then if j = 0 then a else b else if j = 0 then c else d

/-- The coefficient matrix of two-state feedback after eliminating state one. -/
def closure (r : Weight) : Weight :=
  let d := Scalar.star (r 1 1)
  let a := Scalar.star (r 0 0 + r 0 1 * d * r 1 0)
  entries a (a * r 0 1 * d) (d * r 1 0 * a) (d + d * r 1 0 * a * r 0 1 * d)

end Silmaril.Calco2019.CounterSemiring.ThreeCycle.Binary
