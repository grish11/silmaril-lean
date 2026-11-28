module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.StructuralValues.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Blocks.ThreeCycle.Unit.Thms
public import Silmaril.Semantics.Calco2019.Trace.CounterSemiring.ThreeCycle.Thms
public import Mathlib.Data.Matrix.Mul

/-! # A typed polling fragment for the three-cycle matrix candidate -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.MatrixBoundary

open CategoryTheory CategoryTheory.Limits
open Paper.Extension.Singleton
open Paper.Extension.Singleton.ValueCoproducts (exactCopair)
open Silmaril.Calco2019.CounterSemiring.ThreeCycle (Scalar)

inductive Op
  | poll

abbrev U : Ty Empty := .unit
abbrev Reply : Ty Empty := .coprod U U

instance : HasTy Op (Ty Empty) where
  src _ := U
  trg _ := Reply

instance : HasEff Op Bool := ⟨fun _ => true⟩

abbrev Seed := JoinedStep (τ := Ty Empty) (Φ := Op) false
abbrev Obj := ofType Seed
abbrev Native (A : Ty Empty) := Paper.TypeCategory.ofType (Φ := Op) A

/-- The native guard uses literal Unit at the request input and on recurrence. -/
noncomputable def nativeRound : Native U ⟶ Native U ⨿ Native U :=
  let u : Native U ⟶ Native U := Paper.TypeCategory.discardArrow U
  u ≫ Paper.TypeCategory.primitiveReturn Op.poll ≫ (Paper.TypeCategory.sumIso U U).hom ≫
    coprod.map (𝟙 (Native U)) u

/-- The unbatched typed polling step in BinaryFold. Left exits and right repeats. -/
noncomputable def request : Obj U ⟶ Obj Reply :=
  (Paper.Extension.Singleton.projection Seed).map (Paper.TypeCategory.primitiveReturn Op.poll)

/-- Run the next request only on the recursive reply. -/
noncomputable def chain (f g : Obj U ⟶ Obj Reply) : Obj U ⟶ Obj Reply :=
  f ≫ exactCopair Seed (sumCofan Seed U U).inl g

/-- Finite indices for the types of this signature. -/
@[reducible] def arity : Ty Empty → Nat
  | .base a => a.elim
  | .unit => 1
  | .empty => 0
  | .coprod a b => arity a + arity b
  | .product a b => arity a * arity b

abbrev Weight (A B : Ty Empty) := Matrix (Fin (arity A)) (Fin (arity B)) Scalar

/-- The candidate makes an immediate exit with weight one and a repeat
with the order-three generator. -/
def pollMatrix : Weight U Reply :=
  Matrix.of fun _ j => if j = 0 then 1 else Scalar.generator

/-- The local matrix for a Unit step followed, on recurrence, by a second step. -/
def sequenceMatrix (a b : Weight U Reply) : Weight U Reply :=
  Matrix.of fun _ j => a 0 0 * (if j = 0 then 1 else 0) + a 0 1 * b 0 j

/-- One-state matrix feedback is scalar elimination. -/
def feedbackMatrix (a : Weight U Reply) : Weight U U :=
  Matrix.of fun _ _ => Scalar.iterate (a 0 1) (a 0 0)

/-- The three rows are the typed request with its repeat column routed
to the next phase. Column zero is the outward Unit result. -/
def cycleMatrix : Matrix (Fin 3) (Fin 4) Scalar :=
  Matrix.of fun i j => if j = 0 then 1
    else if j = (i + 1).succ then Scalar.generator else 0

/-- The function matrix for the constructor `fun _ => ()`. -/
def forgetMatrix : Matrix (Fin 3) (Fin 1) Scalar :=
  Matrix.of fun _ _ => 1

/-- Preserve the exit column and identify the three repeat columns. -/
def forgetOutputMatrix : Matrix (Fin 4) (Fin 2) Scalar :=
  Matrix.of fun i j => if (i = 0 ∧ j = 0) ∨ (i ≠ 0 ∧ j = 1) then 1 else 0

/-- Keep three original entry rows while eliminating the copied state rows. -/
def cycleNetwork (step : Matrix (Fin 3) (Fin 4) Scalar) : Matrix (Fin 6) (Fin 4) Scalar :=
  Matrix.of fun i j => step ⟨i.val % 3, Nat.mod_lt _ (by decide)⟩ j

/-- One tail-first elimination update in the three-copy matrix. -/
def eliminatePhase (m : Matrix (Fin 6) (Fin 4) Scalar) (i : Fin 3) :
    Matrix (Fin 6) (Fin 4) Scalar :=
  let state : Fin 6 := ⟨i.val + 3, Nat.add_lt_add_right i.isLt 3⟩
  Matrix.of fun entry j => m entry j + m entry i.succ * Scalar.star (m state i.succ) * m state j

/-- The candidate evaluates the three recursive phases from last to first. -/
def cycleFeedback (step : Matrix (Fin 3) (Fin 4) Scalar) : Matrix (Fin 3) (Fin 1) Scalar :=
  Matrix.of fun i _ => (eliminatePhase (eliminatePhase (eliminatePhase (cycleNetwork step) 2) 1) 0)
    (i.castLE (by decide)) 0

/-- The exact matrix for `[inl, step]`, where column zero is the exit. -/
def cycleContinuation (step : Matrix (Fin 3) (Fin 4) Scalar) : Matrix (Fin 4) (Fin 4) Scalar :=
  Matrix.of (Fin.cases (fun j => if j = 0 then 1 else 0) step)

/-- The restrictions of matrix denotation needed by the polling fragment.
Composition is matrix multiplication. The two reply injections are their
function matrices. Unit feedback eliminates its sole recurrence state. -/
structure Lift where
  map {A B : Ty Empty} : (Obj A ⟶ Obj B) → Weight A B
  map_comp {A B D : Ty Empty} (f : Obj A ⟶ Obj B) (g : Obj B ⟶ Obj D) :
    map (f ≫ g) = map f * map g
  inl : map (A := U) (B := Reply) (sumCofan Seed U U).inl = Matrix.of (fun _ j => if j = 0 then 1 else 0)
  inr : map (A := U) (B := Reply) (sumCofan Seed U U).inr = Matrix.of (fun _ j => if j = 1 then 1 else 0)
  poll : map request = pollMatrix
  feedback (f : Obj U ⟶ Obj Reply) :
    map (iterateSum Seed f) 0 0 = Scalar.iterate (map f 0 1) (map f 0 0)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.MatrixBoundary
