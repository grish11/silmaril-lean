module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Calls.ProductBind.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.FiniteExit.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.Defs

/-! # Computed sum elimination at ordered outward exits -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Native.SumBind

open Region.Paper

universe u v w

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- The outward replay closure with the existing computed discriminator step.
Constructor case β is already present in the native rules. -/
abbrev Seed {ε : Type w} [HasEff Φ ε] (pe : ε) :=
  WithCaseBind.JoinedStep (ProductBind.Seed (τ := τ) (Φ := Φ) pe)

abbrev Eqv {ε : Type w} [HasEff Φ ε] (pe : ε) :=
  Extension.Eqv (Seed (τ := τ) (Φ := Φ) pe)

/-- The request list and native outward label of each returning path. A variable
discriminator preserves arm order. An empty elimination contributes no return path. -/
inductive Schedule : VCtx τ → Region Φ → LCtx τ → List (List Φ × Nat) → Prop where
  | ret {Γ : VCtx τ} {L : LCtx τ} {i : Nat} {a : Tm Φ} {A : τ}
      (exit : At L i A) (value : Tm.BranchValue Γ a A) : Schedule Γ (.br i a) L [([], i)]
  | call {Γ : VCtx τ} {L : LCtx τ} {f : Φ} {a : Tm Φ} {r : Region Φ} {paths : List (List Φ × Nat)}
      (value : Tm.BranchValue Γ a (instrSrc f))
      (body : Schedule (instrTrg f :: Γ) r L paths) :
      Schedule Γ (.let₁ (.op f a) r) L (paths.map fun route => (f :: route.1, route.2))
  | caseVar {Γ : VCtx τ} {L : LCtx τ} {slot : Nat} {A B : τ} {l r : Region Φ}
      {left right : List (List Φ × Nat)}
      (value : At Γ slot (coprod A B)) (hl : Schedule (A :: Γ) l L left)
      (hr : Schedule (B :: Γ) r L right) : Schedule Γ (.case (.var slot) l r) L (left ++ right)
  | unpackVar {Γ : VCtx τ} {L : LCtx τ} {slot : Nat} {A B : τ} {r : Region Φ}
      {paths : List (List Φ × Nat)} (value : At Γ slot (product A B))
      (body : Schedule (B :: A :: Γ) r L paths) : Schedule Γ (.let₂ (.var slot) r) L paths

  | abortValue {Γ : VCtx τ} {L : LCtx τ} {A : τ} {a : Tm Φ} {r : Region Φ}
      {paths : List (List Φ × Nat)} (value : Tm.BranchValue Γ a empty)
      (dead : Schedule (A :: Γ) r L paths) : Schedule Γ (.let₁ (.abort a) r) L []

/-- The three possible terminal routes of a straight-line sum producer,
with all its requests before the selected arm's requests. -/
def CasePaths (before left right : List Φ) (i j : Nat) (paths : List (List Φ × Nat)) : Prop :=
  paths = [(before ++ left, i)] ∨ paths = [(before ++ right, j)] ∨
    paths = [(before ++ left, i), (before ++ right, j)]

end Silmaril.Isotope.LambdaSSA.Acyclic.Native.SumBind
