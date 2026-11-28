module

public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Typed.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Semantics.ITree.TypedLabels

/-! # Compare typed and erased Kleisli dispatcher iteration -/

public section

universe v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Interaction.Typed

open CategoryTheory.Limits Silmaril.Elgot
open Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Semantics
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed
open Silmaril.Isotope.Semantics (encodeValue)

variable {κ : Type v} [AtomValues κ]
  {m : Type v → Type v} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]

attribute [local instance] typeModel

local notation "V" => AtomValues.carrier (κ := κ)

/-- Re-encode output and recursive state, using the lawful Elgot equations. -/
private theorem transport {A B C D : Type v}
    (f : A → m (B ⊕ A)) (g : C → m (D ⊕ C)) (out : B → D) (enc : A → C)
    (square : ∀ a, (f a >>= fun s => pure (Sum.map out enc s)) = g (enc a)) (a : A) :
    (iter f a >>= fun b => pure (out b)) = iter g (enc a) := by
  let f' := mapReturn f (fun b => pure (out b))
  have commute : (f' >=> liftPure (Sum.map id enc)) = (liftPure enc >=> g) := by
    funext a
    simp only [f', mapReturn, Bind.kleisliRight, liftPure, Function.comp_apply, bind_assoc, pure_bind]
    rw [← square a]
    exact bind_congr (fun s => by cases s <;> simp)
  calc
    _ = iter f' a := congrFun (LawfulElgotMonad.naturality f (fun b => pure (out b))) a
    _ = _ := by
      simpa [Bind.kleisliRight, liftPure] using congrFun (LawfulElgotMonad.uniformity f' g enc commute) a

theorem cfgDenotation_erased {Γ : VCtx (Ty κ)} {n : Nat} (R : Fin n → Ty κ) (L : LCtx (Ty κ))
    (entry : Monadic.Env Γ → m (Monadic.LabelValue (List.ofFn R ++ L)))
    (collective : Monadic.Env Γ × Monadic.FiniteLabelDen R → m (Monadic.LabelValue (List.ofFn R ++ L)))
    (rawEntry : m (Transfer (Sigma V))) (rawBlock : BlockInput (Sigma V) n → m (Transfer (Sigma V)))
    (ρ : Monadic.Env Γ)
    (he : (entry ρ >>= fun x => pure (encodeLabel (List.ofFn R ++ L) x)) = rawEntry)
    (hb : ∀ x, (collective (ρ, x) >>= fun y => pure (encodeLabel (List.ofFn R ++ L) y)) =
      rawBlock (encodeBlock x)) :
    (Monadic.cfgDenotation entry collective ρ >>= fun x => pure (encodeLabel L x)) =
      (rawEntry >>= fun x =>
        Sum.elim pure (iter (fun p => rawBlock p >>= fun y => pure (splitTransfer n y))) (splitTransfer n x)) := by
  let f := fun current : Monadic.LabelValue (List.ofFn R) =>
    collective (ρ, Monadic.labelDenToFinite R current) >>= fun x =>
      (pure (Monadic.LabelValue.appendSplit (List.ofFn R) L x) :
        m (Monadic.LabelValue L ⊕ Monadic.LabelValue (List.ofFn R)))
  let g := fun p : BlockInput (Sigma V) n =>
    rawBlock p >>= fun x => (pure (splitTransfer n x) : m _)
  let enc := encodeBlock ∘ Monadic.labelDenToFinite R
  have loop (a : Monadic.LabelValue (List.ofFn R)) :
      (iter f a >>= fun x => pure (encodeLabel L x)) = iter g (enc a) := by
    apply transport
    intro current
    simp only [f, g, enc, Function.comp_apply]
    rw [← hb, bind_assoc, bind_assoc]
    simp only [pure_bind, encodeBlock_split]
  simp only [Monadic.cfgDenotation, Monadic.binaryCoproductIso_hom_labelAppendSplit,
    ← he, bind_assoc, pure_bind]
  apply bind_congr
  intro x
  rw [← encodeBlock_split R L]
  cases Monadic.LabelValue.appendSplit (List.ofFn R) L x with
  | inl a => simp
  | inr a => exact loop a

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Interaction.Typed
