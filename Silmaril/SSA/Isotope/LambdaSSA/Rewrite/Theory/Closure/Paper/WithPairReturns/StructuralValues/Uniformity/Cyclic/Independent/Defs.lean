module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Visible.Defs

/-! # Finite reply trees with independently chosen recursive destinations -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent

open CategoryTheory CategoryTheory.Limits
open Cyclic.Visible (choose replyIso)

local notation "Uq" => Cyclic.Visible.One

/-- Uq step may perform any finite tree of visible Boolean polls.
Each branch names its own continuation. -/
inductive ReplyTree (α : Type) where
  | leaf (result : α)
  | poll (onFalse onTrue : ReplyTree α)
  deriving DecidableEq

def ReplyTree.map {α β : Type} (f : α → β) : ReplyTree α → ReplyTree β
  | .leaf a => .leaf (f a)
  | .poll l r => .poll (l.map f) (r.map f)

/-- Interpret each visible request with the given binary-result arrow. -/
noncomputable def ReplyTree.render {C : Type*} [Category C] [HasBinaryCoproducts C] {U Y : C}
    {α : Type} (choose : U ⟶ U ⨿ U) (leaf : α → (U ⟶ Y)) : ReplyTree α → (U ⟶ Y)
  | .leaf a => leaf a
  | .poll l r => choose ≫ coprod.desc (l.render choose leaf) (r.render choose leaf)

inductive Route where
  | exit
  | first
  | second
  deriving DecidableEq

/-- Erase the recursive copy while preserving exit versus recurrence. -/
def Route.recurrent : Route → Bool
  | .exit => false
  | .first | .second => true

def Route.swap : Route → Route
  | .exit => .exit
  | .first => .second
  | .second => .first

noncomputable abbrev fold : Uq ⨿ Uq ⟶ Uq := coprod.desc (𝟙 Uq) (𝟙 Uq)

noncomputable abbrev request : Uq ⟶ Uq ⨿ Uq := choose ≫ replyIso.hom

noncomputable def route : Route → (Uq ⟶ Uq ⨿ (Uq ⨿ Uq))
  | .exit => coprod.inl
  | .first => coprod.inl ≫ coprod.inr
  | .second => coprod.inr ≫ coprod.inr

noncomputable def foldedRoute : Bool → (Uq ⟶ Uq ⨿ Uq)
  | false => coprod.inl
  | true => coprod.inr

noncomputable def sourceStep (left right : ReplyTree Route) :
    Uq ⨿ Uq ⟶ Uq ⨿ (Uq ⨿ Uq) :=
  coprod.desc (left.render request route) (right.render request route)

noncomputable def targetStep (row : ReplyTree Bool) : Uq ⟶ Uq ⨿ Uq :=
  row.render request foldedRoute

/-- Both copies can stay, switch, or exit. They agree on one reply prefix
and differ on another, so the second row is not a swap of the first. -/
def fixtureLeft : ReplyTree Route :=
  .poll (.poll (.leaf .first) (.leaf .second)) (.poll (.leaf .first) (.leaf .exit))

def fixtureRight : ReplyTree Route :=
  .poll (.poll (.leaf .first) (.leaf .second)) (.poll (.leaf .second) (.leaf .exit))

def fixtureTarget : ReplyTree Bool :=
  .poll (.poll (.leaf true) (.leaf true)) (.poll (.leaf true) (.leaf false))

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent
