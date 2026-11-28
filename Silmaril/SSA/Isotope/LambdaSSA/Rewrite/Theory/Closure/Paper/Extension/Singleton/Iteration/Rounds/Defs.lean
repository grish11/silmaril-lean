module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Blocks.ThreeCycle.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Discard.Coproducts.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Rounds.Defs

/-! # Several rounds of one guarded step, and the unrolling laws of a quotient -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.Rounds

open CategoryTheory CategoryTheory.Limits
open Silmaril.DeBruijn (lift)
open Silmaril.Isotope.LambdaSSA (VCtx LCtx)
open ValueCoproducts (exactCopair)
open ThreeCycle (triple)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

/-- Run `s`. If it repeats, run `t` on the new state. -/
noncomputable def thenExact {A B : τ} (s t : ofType Seed A ⟶ ofType Seed (Silmaril.coprod B A)) :
    ofType Seed A ⟶ ofType Seed (Silmaril.coprod B A) :=
  s ≫ exactCopair Seed (sumCofan Seed B A).inl t

/-- `rounds s n` runs up to `n + 1` rounds of `s`, stopping at the first return. -/
noncomputable def rounds {A B : τ} (s : ofType Seed A ⟶ ofType Seed (Silmaril.coprod B A)) :
    Nat → (ofType Seed A ⟶ ofType Seed (Silmaril.coprod B A))
  | 0 => s
  | n + 1 => thenExact Seed s (rounds s n)

/-- The written form: the repeat arm of `s` continues with `t` and its
return arm keeps the returned value. -/
def thenRegion (s t : Region Φ) : Region Φ :=
  s.lsubst (fun _ => (Region.case (.var 0) ((Region.br 0 (.inl (.var 0))).renameVars (lift Nat.succ))
    (t.renameVars (lift Nat.succ))).renameVars (lift Nat.succ))

def roundsRegion (s : Region Φ) : Nat → Region Φ
  | 0 => s
  | n + 1 => thenRegion s (roundsRegion s n)

/-- The quotient equates the loop on `n + 1` rounds with the loop on one. -/
def Unrolls (n : Nat) : Prop :=
  ∀ {A B : τ} (s : ofType Seed A ⟶ ofType Seed (Silmaril.coprod B A)),
    iterateSum Seed (rounds Seed s n) = iterateSum Seed s

/-- The same law at the chosen coproduct of the quotient. -/
def RoundsLaw (n : Nat) : Prop :=
  ∀ {X Y : TypeCategory Seed} (g : X ⟶ Y ⨿ X),
    iterateChosen Seed (Silmaril.Isotope.LambdaSSA.Semantics.Categorical.roundsStep g n) =
      iterateChosen Seed g

/-- The two-round law at the chosen coproduct. -/
def Doubles : Prop :=
  ∀ {X Y : TypeCategory Seed} (g : X ⟶ Y ⨿ X),
    iterateChosen Seed (g ≫ coprod.desc coprod.inl g) = iterateChosen Seed g

/-- The three-round law at the chosen coproduct. -/
def Triples : Prop :=
  ∀ {X Y : TypeCategory Seed} (g : X ⟶ Y ⨿ X), iterateChosen Seed (triple g) = iterateChosen Seed g

/-- `Smooth n` holds when the round count `n + 1` is a product of twos and threes. -/
inductive Smooth : Nat → Prop
  | one : Smooth 0
  | double {m : Nat} : Smooth m → Smooth (2 * m + 1)
  | triple {m : Nat} : Smooth m → Smooth (3 * m + 2)

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.Rounds
