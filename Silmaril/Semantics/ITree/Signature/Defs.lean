module

public import Silmaril.Semantics.ITree.Reindex.Thms
public import Mathlib.CategoryTheory.Category.Basic

/-! # Interaction-tree signatures and translations -/

@[expose] public section

namespace Silmaril.Elgot.ITree

universe u v w

/-- An effect signature is an indexed family of requests. The index is the reply type. -/
structure Signature where
  Event : Type u → Type u

namespace Signature

/-- The request map is covariant; a target reply is fed back to the source continuation.
Neither function is required to be injective or surjective. -/
structure Hom (S T : Signature.{u}) where
  request : Request S.Event → Request T.Event
  reply (q : Request S.Event) : (request q).1 → q.1

open CategoryTheory

instance : Category Signature.{u} where
  Hom := Hom
  id _ := ⟨id, fun _ => id⟩
  comp f g := ⟨fun q => g.request (f.request q), fun q r => f.reply q (g.reply (f.request q) r)⟩

variable {S T U : Signature.{u}} {A : Type v} {B : Type w}

/-- Forget the inverses of a typed request and reply equivalence. -/
def ofEquiv (e : SignatureEquiv S.Event T.Event) : S ⟶ T :=
  ⟨e.request, fun q => (e.reply q).symm⟩

/-- The disjoint union of two effect signatures. -/
def sum (S T : Signature.{u}) : Signature.{u} := ⟨fun R => S.Event R ⊕ T.Event R⟩

def inl (S T : Signature.{u}) : S ⟶ S.sum T :=
  ⟨fun q => ⟨q.1, .inl q.2⟩, fun _ => id⟩

def inr (S T : Signature.{u}) : T ⟶ S.sum T :=
  ⟨fun q => ⟨q.1, .inr q.2⟩, fun _ => id⟩

/-- Define a morphism out of a sum by giving its action on each summand. -/
def desc (f : S ⟶ U) (g : T ⟶ U) : S.sum T ⟶ U where
  request
    | ⟨R, .inl ev⟩ => f.request ⟨R, ev⟩
    | ⟨R, .inr ev⟩ => g.request ⟨R, ev⟩
  reply
    | ⟨R, .inl ev⟩ => f.reply ⟨R, ev⟩
    | ⟨R, .inr ev⟩ => g.reply ⟨R, ev⟩

def Hom.visible (f : S ⟶ T) (a : A → B) {X : Type*} {Y : Type*}
    (k : X → Y) : Visible S.Event A X → Visible T.Event B Y
  | .ret b => .ret (a b)
  | @Visible.vis _ _ _ R ev next =>
      let q : Request S.Event := ⟨R, ev⟩
      .vis (f.request q).2 (fun r => k (next (f.reply q r)))

def Hom.approx (f : S ⟶ T) (a : A → B) :
    (n : Nat) → Approx S.Event A n → Approx T.Event B n
  | 0, _ => PUnit.unit
  | n + 1, obs => Part.map (f.visible a (f.approx a n)) obs

/-- Reduct of a handler existentially hides the extra information in a target reply. -/
def Hom.restrict (f : S ⟶ T) {X : Type v} (step : Handler X T.Event) : Handler X S.Event :=
  fun q x r y => ∃ r', f.reply q r' = r ∧ step (f.request q) x r' y

end Signature

end Silmaril.Elgot.ITree
