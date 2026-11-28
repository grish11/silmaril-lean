module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Exits.Defs

/-! # Check written constructor routes without a semantic witness -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA

variable {κ : Type u} {Φ : Type v} [HasTy Φ (Ty κ)]

/-- The expression forms admitted in branch operands and case tests.
Injections are checked at the branch boundary, where the tag is known. -/
def Tm.synthRouteType? [DecidableEq κ] (Γ : VCtx (Ty κ)) : Tm Φ → Option (Ty κ)
  | .var i => Γ[i]?
  | .op p a => (a.synthRouteType? Γ).bind fun A =>
      if A = instrSrc p then some (instrTrg p) else none
  | .unit => some .unit
  | .pair a b => (a.synthRouteType? Γ).bind fun A =>
      (b.synthRouteType? Γ).bind fun B => some (.product A B)
  | _ => none

/-- At a tagged label, read back the operand of the specified injection. -/
def Tm.routePayload? (tag : Option CaseTag) (a : Tm Φ) : Option (Tm Φ) :=
  match tag, a with
  | none, _ => some a
  | some .inl, .inl b => some b
  | some .inr, .inr b => some b
  | some _, _ => none

/-- Each destination carries the indicated payload, wrapped in the given
injection for a selected row. A plain destination needs no wrapper. -/
abbrev RouteLayout (κ : Type u) := List (Ty κ × Option CaseTag)

/-- Read a common row from a written wide row. Both arms of a case are
checked at their synthesized exact types. Unsupported nodes give none. -/
def Region.checkRoutes? [DecidableEq κ] (layout : RouteLayout κ) (Γ : VCtx (Ty κ)) :
    Region Φ → Option (Region Φ)
  | .br i arg =>
      match layout[i]? with
      | none => none
      | some (A, tag) => (arg.routePayload? tag).bind fun a =>
          match a.synthRouteType? Γ with
          | some B => if A = B then some (.br i a) else none
          | none => none
  | .case a l r =>
      match a.synthRouteType? Γ with
      | some (.coprod A B) =>
          (l.checkRoutes? layout (A :: Γ)).bind fun l' =>
          (r.checkRoutes? layout (B :: Γ)).bind fun r' => some (.case a l' r')
      | _ => none
  | _ => none

open Semantics.Categorical in
/-- The type and route data read from a successful written-row check. -/
inductive CheckedRoutes (layout : RouteLayout κ) : VCtx (Ty κ) → Region Φ → Region Φ → Prop where
  | plain {Γ i a A} (hit : layout[i]? = some (A, none)) (typed : a.HasType Γ A)
      (arg : DeterminedTerm Γ a A) : CheckedRoutes layout Γ (.br i a) (.br i a)
  | tagged {Γ i a A tag} (hit : layout[i]? = some (A, some tag)) (typed : a.HasType Γ A)
      (arg : DeterminedTerm Γ a A) : CheckedRoutes layout Γ (.br i a) (.br i (tag.inject a))
  | case {Γ a l r l' r' A B} (typed : a.HasType Γ (.coprod A B))
      (unique : TypeDetermined Γ a (.coprod A B)) (arg : DeterminedTerm Γ a (.coprod A B))
      (yes : CheckedRoutes layout (A :: Γ) l l') (no : CheckedRoutes layout (B :: Γ) r r') :
      CheckedRoutes layout Γ (.case a l r) (.case a l' r')

end Silmaril.Isotope.LambdaSSA
