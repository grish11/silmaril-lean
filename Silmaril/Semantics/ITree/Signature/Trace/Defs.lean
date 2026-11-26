module

public import Silmaril.Semantics.ITree.Signature.Thms
public import Mathlib.CategoryTheory.Functor.Basic

/-! # Signature arrows for finite trace predicates -/

@[expose] public section

namespace Silmaril.Elgot.ITree

open CategoryTheory

universe u v

/-- The same objects as `Signature`, with arrows that embed packed requests and
preserve all reply information at each request. -/
structure TraceSignature where
  toSignature : Signature.{u}

namespace TraceSignature

/-- Reply bijectivity is a property of the original backward reply function. -/
structure Hom (S T : TraceSignature.{u}) where
  hom : S.toSignature ⟶ T.toSignature
  request_injective : Function.Injective hom.request
  reply_bijective (q : Request S.toSignature.Event) : Function.Bijective (hom.reply q)

instance : Category TraceSignature.{u} where
  Hom := Hom
  id S := ⟨𝟙 S.toSignature, Function.injective_id, fun _ => Function.bijective_id⟩
  comp f g := ⟨f.hom ≫ g.hom, g.request_injective.comp f.request_injective,
    fun q => (f.reply_bijective q).comp (g.reply_bijective (f.hom.request q))⟩

/-- Forget the restrictions on arrows to recover the return institution's signatures. -/
def forget : TraceSignature.{u} ⥤ Signature.{u} where
  obj := toSignature
  map f := f.hom

variable {S T : TraceSignature.{u}} {A : Type v}

/-- A typed signature equivalence is a trace arrow. -/
def ofEquiv (e : SignatureEquiv S.toSignature.Event T.toSignature.Event) : S ⟶ T :=
  ⟨Signature.ofEquiv e, e.request.injective, fun q => (e.reply q).symm.bijective⟩

/-- Include the left summand without changing its replies. -/
def inl (S T : Signature.{u}) : (⟨S⟩ : TraceSignature) ⟶ ⟨S.sum T⟩ :=
  ⟨Signature.inl S T, fun _ _ h => Option.some.inj (congrArg (fun
    | ⟨R, .inl ev⟩ => some (⟨R, ev⟩ : Request S.Event)
    | ⟨_, .inr _⟩ => none) h), fun _ => Function.bijective_id⟩

/-- Include the right summand without changing its replies. -/
def inr (S T : Signature.{u}) : (⟨T⟩ : TraceSignature) ⟶ ⟨S.sum T⟩ :=
  ⟨Signature.inr S T, fun _ _ h => Option.some.inj (congrArg (fun
    | ⟨_, .inl _⟩ => none
    | ⟨R, .inr ev⟩ => some (⟨R, ev⟩ : Request T.Event)) h), fun _ => Function.bijective_id⟩

/-- The equivalence in the original, backward direction. -/
noncomputable def Hom.replyEquiv (f : S ⟶ T) (q : Request S.toSignature.Event) :
    (f.hom.request q).1 ≃ q.1 :=
  Equiv.ofBijective (f.hom.reply q) (f.reply_bijective q)

/-- Rename a finite observation, using the inverse of the backward reply map
at each completed exchange. A pending request carries no reply to translate. -/
noncomputable def Hom.trace (f : S ⟶ T) :
    Trace S.toSignature.Event A → Trace T.toSignature.Event A
  | .prefix => .prefix
  | .request ev => .request (f.hom.request ⟨_, ev⟩).2
  | .exchange ev r tail =>
      .exchange (f.hom.request ⟨_, ev⟩).2 ((f.replyEquiv ⟨_, ev⟩).symm r) (f.trace tail)
  | .result a => .result a

end TraceSignature

end Silmaril.Elgot.ITree
