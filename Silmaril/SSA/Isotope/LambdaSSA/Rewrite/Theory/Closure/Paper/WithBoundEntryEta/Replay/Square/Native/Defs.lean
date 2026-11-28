module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Case.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Coproducts.Thms

/-! # Standard Paper frames for a guarded recurrent round -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.NativeFrame

open CategoryTheory CategoryTheory.Limits
open Paper.TypeCategory (ofType ofRegion sumCofan sumIso)
open Silmaril.DeBruijn (lift)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {A B D E I X Y L R : τ}

local notation "Obj" => ofType (Φ := Φ)
local notation "State" => Silmaril.coprod X Y

open Generators (weakenRows)

/-- Run an initializer before a table whose entry evaluates a discriminator.
The rows are scoped before the initializer binder. -/
def letCaseTable {n : Nat} (init disc : Tm Φ) (left right : Region Φ) (rows : Fin n → Region Φ) : Region Φ :=
  .let₁ init (.cfg (.case disc left right) n (weakenRows rows))

/-- Replace the sole outward exit of the round with a constructor repeat. -/
def repeating (work : Region Φ) (reply : Tm Φ) : Region Φ :=
  compLSubst (fun _ => work) (fun _ => .br 0 (.inr reply)) 0

noncomputable def linear (h : Obj A ⟶ Obj D) (work : Obj D ⟶ Obj E) (next : Obj E ⟶ Obj A) :
    Obj A ⟶ Obj B ⨿ Obj A :=
  h ≫ work ≫ next ≫ coprod.inr

/-- Run one common round after precomposing with the state map on either
input arm, then route the reply to that arm's specified next state. -/
noncomputable def split (h : Obj State ⟶ Obj D) (work : Obj D ⟶ Obj E)
    (nextLeft nextRight : Obj E ⟶ Obj State) : Obj State ⟶ Obj B ⨿ Obj State :=
  (sumIso X Y).hom ≫ coprod.desc
    ((sumCofan X Y).inl ≫ h ≫ work ≫ nextLeft ≫ coprod.inr)
    ((sumCofan X Y).inr ≫ h ≫ work ≫ nextRight ≫ coprod.inr)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.NativeFrame
