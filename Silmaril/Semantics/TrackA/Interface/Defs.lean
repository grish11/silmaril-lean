module

public import Mathlib.Logic.Equiv.Defs
public import Silmaril.Semantics.TrackA.Interaction.Defs

/-! # Sequential interaction interfaces

A sub-interface retains the response fiber of each selected request. A renaming
has an equivalence on requests and an equivalence on each response fiber.
Hiding executes one layer at a time using a typed internal response policy.
-/

@[expose] public section

namespace Silmaril.Semantics.TrackA.Interface

open Interaction

universe u v w x y z b c a s

variable {S : Signature.{u,v}} {T : Signature.{w,x}} {U : Signature.{y,z}}

namespace Signature

/-- Select requests by a predicate and retain their dependent response types. -/
def restrict (S : Interaction.Signature.{u,v}) (P : S.Request → Prop) :
    Interaction.Signature.{u,v} where
  Request := {q : S.Request // P q}
  Response q := S.Response q.val

def inclusion (P : S.Request → Prop) : Interaction.Signature.Hom (restrict S P) S :=
  ⟨Subtype.val, fun _ r => r⟩

/-- Factor a translation through the restriction if every translated request lies in it. -/
def factor (P : T.Request → Prop) (f : Interaction.Signature.Hom S T)
    (lands : ∀ q, P (f.request q)) : Interaction.Signature.Hom S (restrict T P) :=
  ⟨fun q => ⟨f.request q, lands q⟩, f.response⟩

/-- Disjoint signature composition. Each response fiber is lifted into the
common universe, and the injections decode it with `ULift.down`. -/
def sum (S : Interaction.Signature.{u,v}) (T : Interaction.Signature.{w,x}) :
    Interaction.Signature.{max u w, max v x} where
  Request := S.Request ⊕ T.Request
  Response
    | .inl q => ULift.{x} (S.Response q)
    | .inr q => ULift.{v} (T.Response q)

def inl (S : Interaction.Signature.{u,v}) (T : Interaction.Signature.{w,x}) :
    Interaction.Signature.Hom S (sum S T) :=
  ⟨Sum.inl, fun _ r => r.down⟩

def inr (S : Interaction.Signature.{u,v}) (T : Interaction.Signature.{w,x}) :
    Interaction.Signature.Hom T (sum S T) :=
  ⟨Sum.inr, fun _ r => r.down⟩

def copair (f : Interaction.Signature.Hom S U) (g : Interaction.Signature.Hom T U) :
    Interaction.Signature.Hom (sum S T) U where
  request := Sum.elim f.request g.request
  response
    | .inl q => fun r => ⟨f.response q r⟩
    | .inr q => fun r => ⟨g.response q r⟩

end Signature

/-- A coherent renaming gives invertible translations of both requests and replies. -/
structure Renaming (S : Interaction.Signature.{u,v}) (T : Interaction.Signature.{w,x}) where
  request : S.Request ≃ T.Request
  response (q : S.Request) : S.Response q ≃ T.Response (request q)

namespace Renaming

def id (S : Interaction.Signature.{u,v}) : Renaming S S :=
  ⟨Equiv.refl _, fun _ => Equiv.refl _⟩

def comp (g : Renaming T U) (f : Renaming S T) : Renaming S U :=
  ⟨f.request.trans g.request, fun q => (f.response q).trans (g.response (f.request q))⟩

def symm (f : Renaming S T) : Renaming T S :=
  ⟨f.request.symm, fun q =>
    (Equiv.cast (congrArg T.Response (f.request.apply_symm_apply q).symm)).trans
      (f.response (f.request.symm q)).symm⟩

/-- Relabeling decodes target replies to drive the source continuation. -/
def toHom (f : Renaming S T) : Interaction.Signature.Hom S T :=
  ⟨f.request, fun q => (f.response q).symm⟩

/-- Flatten nested restrictions when every request visible at the second
stage is visible at the first. The response types are definitionally equal. -/
def flatten {P Q : S.Request → Prop} (subset : ∀ q, P q → Q q) :
    Renaming (Signature.restrict (Signature.restrict S Q) (fun q => P q.val))
      (Signature.restrict S P) where
  request :=
    { toFun := fun q => ⟨q.val.val, q.property⟩
      invFun := fun q => ⟨⟨q.val, subset q.val q.property⟩, q.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  response _ := Equiv.refl _

end Renaming

namespace Coalgebra

open Interaction (Node)

variable {B : Interaction.Signature.{b,c}} {A : Type a} {X : Type s}

/-- Apply a signature morphism at each unfolding, with the same state carrier. -/
def relabel (f : Interaction.Signature.Hom S T) (c : Interaction.Coalgebra S B A X) :
    Interaction.Coalgebra T B A X :=
  fun x => (c x).relabel f

/-- Extend a component to a disjoint sum. Every request it issues is tagged left. -/
def extend (T : Interaction.Signature.{w,x}) (c : Interaction.Coalgebra S B A X) :
    Interaction.Coalgebra (Signature.sum S T) B A X :=
  relabel (Signature.inl S T) c

/-- A partial internal responder. A reply is typed by the hidden request,
and the policy can consult the current state before replying or refusing. -/
abbrev Policy (S : Interaction.Signature.{u,v}) (P : S.Request → Prop) (X : Type s) :=
  X → (q : S.Request) → ¬P q → Option (S.Response q)

/-- Route a hidden request to the first stage at which it is hidden. -/
def Policy.staged {P Q : S.Request → Prop} [DecidablePred Q] (first : Policy S Q X)
    (second : Policy (Signature.restrict S Q) (fun q => P q.val) X) : Policy S P X :=
  fun x q hidden =>
    if h : Q q then second x ⟨q, h⟩ hidden else first x q h

/-- Forward selected requests with their original continuations. A hidden
request takes one tau step with the supplied reply. A policy result of
`none` returns the supplied `refusal : A`. At a UB boundary with result
type `Option (Except Error Value)`, use `some (.error e)` for ordinary
refusal. Returning the outer `none` is explicit UB at that boundary.
Returns, tau and choice retain their layers. -/
def hide (P : S.Request → Prop) [dec : DecidablePred P] (policy : Policy S P X)
    (refusal : A) (c : Interaction.Coalgebra S B A X) :
    Interaction.Coalgebra (Signature.restrict S P) B A X :=
  fun x =>
    match c x with
    | .ret a => .ret a
    | .tau next => .tau next
    | .branch kind shape next => .branch kind shape next
    | .vis q next =>
      if visible : P q then .vis ⟨q, visible⟩ next
      else
        match policy x q visible with
        | some reply => .tau (next reply)
        | none => .ret refusal

/-- Restrict an implementation to selected requests by refusing every other request. -/
def restrict (P : S.Request → Prop) [DecidablePred P] (refusal : A)
    (c : Interaction.Coalgebra S B A X) :
    Interaction.Coalgebra (Signature.restrict S P) B A X :=
  hide P (fun _ _ _ => none) refusal c

end Coalgebra
end Silmaril.Semantics.TrackA.Interface
