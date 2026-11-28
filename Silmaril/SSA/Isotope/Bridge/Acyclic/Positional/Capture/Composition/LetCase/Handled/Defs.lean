module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Thms
public import Silmaril.SSA.Isotope.LetCase.HandledTrace.Category.Thms

/-! # Product packaging of older captures for one-input programs

A handled-trace program has one typed input and no older slots. An operand
with older captures becomes such a program by carrying every capture beside
its input and returning it beside the result.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled

open Isotope.Semantics (BoundEnv ProductModel)

universe u v w

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- The one input type carrying every older slot beside the input. The
oldest slot is outermost, and an empty context leaves the input unchanged. -/
def wrap : {n : Nat} → BoundCtx τ n → τ → τ
  | _, .nil, X => X
  | _, .snoc β A, X => wrap β (product A X)

/-- Read the newest older slot from a pair with the input, run the operand
on both, and return that slot beside the result. -/
def keep {n : Nat} {β : BoundCtx τ n} {A X Y : τ} (a : Operand Φ ((β.snoc A).snoc X) Y) :
    Operand Φ (β.snoc (product A X)) (product A Y) :=
  let lift := BoundCtx.Renaming.underTwoBinders β (product A X) A X
  ⟨.let₂ (.bv 0) (.pair (.bv 1) (a.1.rename lift.toFun)), .let₂ .bv (.pair .bv (a.2.rename lift))⟩

/-- Retain every older slot, newest first. At the empty context this is the
operand itself. -/
def pack : {n : Nat} → (β : BoundCtx τ n) → {X Y : τ} → Operand Φ (β.snoc X) Y →
    LetCase.HandledTrace.Program Φ (wrap β X) (wrap β Y)
  | _, .nil, _, _, a => a
  | _, .snoc β _, _, _, a => pack β (keep a)

variable {D : τ → Type w} [ProductModel D]

/-- The packed value of an older environment and an input. -/
def wrapValue : {n : Nat} → (β : BoundCtx τ n) → {X : τ} → BoundEnv D β → D X → D (wrap β X)
  | _, .nil, _, _, x => x
  | _, .snoc β A, X, ρ, x =>
    wrapValue β (fun i => ρ i.succ) ((ProductModel.productEquiv A X).symm (ρ 0, x))

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled
