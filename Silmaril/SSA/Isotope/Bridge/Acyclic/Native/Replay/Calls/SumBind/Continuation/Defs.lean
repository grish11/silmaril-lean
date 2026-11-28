module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Calls.SumBind.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Beta.Constructors.Defs

/-! # Returning a computed case into a subsequent primitive -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Native.SumBind.Continuation

open Region.Paper
open Region.Paper.RetainedLet (returnOnce)
open Region.Paper.UnaryReturn.Beta.Constructors (inlSequence inrSequence)
open Silmaril.DeBruijn (lift)

universe u v w

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- Expose the evaluation of an effectful operand at the same singleton
result interface before case analysis, destructuring, tagging or empty elimination. -/
inductive ReturnStep : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop where
  | split {Γ : VCtx τ} {A B D : τ} {e l r : Tm Φ}
      (he : Tm.HasType Γ e (coprod A B)) (hl : Tm.HasType (A :: Γ) l D)
      (hr : Tm.HasType (B :: Γ) r D) :
      ReturnStep Γ (returnOnce (.case e l r)) (.case e (returnOnce l) (returnOnce r)) [D]
  | splitPair {Γ : VCtx τ} {A B D : τ} {a b : Tm Φ}
      (ha : Tm.HasType Γ a (product A B)) (hb : Tm.HasType (B :: A :: Γ) b D) :
      ReturnStep Γ (returnOnce (.let₂ a b)) (.let₂ a (returnOnce b)) [D]
  | splitInl {Γ : VCtx τ} {A B : τ} {a : Tm Φ} (ha : Tm.HasType Γ a A) :
      ReturnStep Γ (returnOnce (.inl a)) (inlSequence a) [coprod A B]
  | splitInr {Γ : VCtx τ} {A B : τ} {a : Tm Φ} (ha : Tm.HasType Γ a B) :
      ReturnStep Γ (returnOnce (.inr a)) (inrSequence a) [coprod A B]
  | splitAbort {Γ : VCtx τ} {D : τ} {a : Tm Φ} (ha : Tm.HasType Γ a empty) :
      ReturnStep Γ (returnOnce (.abort a)) (.let₁ a (returnOnce (.abort (.var 0)))) [D]

abbrev Seed {ε : Type w} [HasEff Φ ε] (pe : ε)
    (Γ : VCtx τ) (p q : Region Φ) (L : LCtx τ) : Prop :=
  SumBind.Seed pe Γ p q L ∨ ReturnStep Γ p q L

abbrev Eqv {ε : Type w} [HasEff Φ ε] (pe : ε) :=
  Extension.Eqv (Seed (τ := τ) (Φ := Φ) pe)

/-- A continuation on the case result runs one primitive. Its body sees
the primitive reply and the original captures, with the argument slot fresh. -/
def invoke (f : Φ) (body : Region Φ) : Region Φ :=
  .let₁ (.op f (.var 0)) (body.renameVars (lift Nat.succ))

/-- Each producer path is followed by one call and a path of the body.
The final label belongs to the body's original ordered exits. -/
def callPaths (f : Φ) (before after : List (List Φ × Nat)) : List (List Φ × Nat) :=
  before.flatMap fun a => after.map fun b => (a.1 ++ f :: b.1, b.2)

end Silmaril.Isotope.LambdaSSA.Acyclic.Native.SumBind.Continuation
