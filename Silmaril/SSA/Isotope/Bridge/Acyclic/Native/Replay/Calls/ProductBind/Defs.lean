module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Calls.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.BinaryLetBind.Defs

/-! # Product elimination in outward call replay -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Native.ProductBind

open Region.Paper Region.Paper.WithComputedCallReturns
open Silmaril.DeBruijn (lift)

universe u v w

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- The #4450 closure together with the existing Figure 19 binary-let
binding step. Constructor-pair beta is already a Paper equation. -/
abbrev Seed {ε : Type w} [HasEff Φ ε] (pe : ε)
    (Γ : VCtx τ) (r s : Region Φ) (L : LCtx τ) : Prop :=
  OrderedPairs.Seed pe Γ r s L ∨ Region.BinaryLetBind.Step Γ r s L

abbrev Eqv {ε : Type w} [HasEff Φ ε] (pe : ε) :=
  Extension.Eqv (Seed (τ := τ) (Φ := Φ) pe)

/-- Continuation for a single product-valued transfer. Its new packet
slot is fresh for the original body, including below both field binders. -/
def unpack (k : Region Φ) : Region Φ :=
  .let₂ (.var 0) (k.renameVars (lift (lift Nat.succ)))

/-- Requests with constructor arguments and pure destructures of a
product slot. Returns keep their original label in the ordered exits. -/
inductive Schedule : VCtx τ → Region Φ → LCtx τ → List Φ → Prop where
  | ret {Γ : VCtx τ} {L : LCtx τ} {i : Nat} {a : Tm Φ} {A : τ}
      (exit : At L i A) (value : Tm.BranchValue Γ a A) : Schedule Γ (.br i a) L []
  | call {Γ : VCtx τ} {L : LCtx τ} {f : Φ} {a : Tm Φ} {r : Region Φ} {fs : List Φ}
      (value : Tm.BranchValue Γ a (instrSrc f))
      (body : Schedule (instrTrg f :: Γ) r L fs) : Schedule Γ (.let₁ (.op f a) r) L (f :: fs)
  | unpackVar {Γ : VCtx τ} {L : LCtx τ} {i : Nat} {A B : τ} {r : Region Φ} {fs : List Φ}
      (value : At Γ i (product A B)) (body : Schedule (B :: A :: Γ) r L fs) :
      Schedule Γ (.let₂ (.var i) r) L fs

end Silmaril.Isotope.LambdaSSA.Acyclic.Native.ProductBind
