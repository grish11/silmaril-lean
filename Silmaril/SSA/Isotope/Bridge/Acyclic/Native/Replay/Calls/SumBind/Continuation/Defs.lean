module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Calls.SumBind.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Defs

/-! # Returning a computed case into a subsequent primitive -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Native.SumBind.Continuation

open Region.Paper
open Region.Paper.RetainedLet (returnOnce)
open Silmaril.DeBruijn (lift)

universe u v w

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- Expose a returned case as a region case at its singleton result
interface. The discriminator and both arms can have effects. -/
inductive ReturnStep : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop where
  | split {Γ : VCtx τ} {A B D : τ} {e l r : Tm Φ}
      (he : Tm.HasType Γ e (coprod A B)) (hl : Tm.HasType (A :: Γ) l D)
      (hr : Tm.HasType (B :: Γ) r D) :
      ReturnStep Γ (returnOnce (.case e l r)) (.case e (returnOnce l) (returnOnce r)) [D]

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
