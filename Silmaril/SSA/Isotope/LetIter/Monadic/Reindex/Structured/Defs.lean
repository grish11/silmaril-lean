module

public import Silmaril.SSA.Isotope.LetIter.Monadic.Reindex.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Defs

/-! # Transport for structured LetIter requests -/

@[expose] public section

namespace Silmaril.Isotope.LetIter.Reindex.Structured

open Silmaril.Isotope.Semantics Silmaril.Elgot
open PaperExpression.Source.FreeTree.Response.Structured (Event Lifted toSmall)

universe u

variable {α Φ : Type u} [HasTy Φ (Ty α)] {V W : α → Type u}

/-- Lift a carrier equivalence to the universe of the evaluator. -/
def liftedEquiv (e : ∀ a, V a ≃ W a) (a : α) : Lifted V a ≃ Lifted W a :=
  (Equiv.ulift.trans (e a)).trans Equiv.ulift.symm

/-- A packed structured event is exactly a primitive paired with its operand. -/
def requestEquiv (V : α → Type u) :
    ITree.Request (Event (Φ := Φ) V) ≃ ((f : Φ) × Ty.denote V (instrSrc f)) where
  toFun
    | ⟨_, .call f x⟩ => ⟨f, x⟩
  invFun
    | ⟨f, x⟩ => ⟨_, .call f x⟩
  left_inv := fun ⟨_, .call _ _⟩ => rfl
  right_inv := fun ⟨_, _⟩ => rfl

/-- Keep the primitive symbol and transport its operand and reply at their
declared types. -/
def signatureEquiv (e : ∀ a, V a ≃ W a) :
    ITree.SignatureEquiv (Event (Φ := Φ) V) (Event (Φ := Φ) W) where
  request := (requestEquiv V).trans
    ((Equiv.sigmaCongrRight fun f => typeEquiv e (instrSrc f)).trans (requestEquiv W).symm)
  reply
    | ⟨_, .call f _⟩ => typeEquiv e (instrTrg f)

/-- Interpret every primitive as a visible typed call followed by its reply. -/
def callInstructions (V : α → Type u) :
    InstructionModel (Ty.denote (Lifted V)) Φ (ITree.Tree (Event (Φ := Φ) V)) where
  eval f x := ITree.vis (.call f (toSmall V (instrSrc f) x)) fun r =>
    ITree.ret ((toSmall V (instrTrg f)).symm r)

end Silmaril.Isotope.LetIter.Reindex.Structured
