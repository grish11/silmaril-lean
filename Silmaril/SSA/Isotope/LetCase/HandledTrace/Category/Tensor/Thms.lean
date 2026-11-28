module

public import Silmaril.SSA.Isotope.LetCase.HandledTrace.Category.Tensor.Defs
import Silmaril.Proofs.SSA.Isotope.LetCase.HandledTrace.Category.Tensor.Laws

@[expose] public section

namespace Silmaril.Isotope.LetCase.HandledTrace

open CategoryTheory Silmaril.Isotope.Semantics Silmaril.Elgot.ITree
open Silmaril.Isotope.Refinement.Models (EnrichedFunctor)

universe u v e s

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {D : τ → Type (e + 1)} [ProductModel D] [UnitModel D] [CoproductModel D] [EmptyModel D]
  {Events : Type e → Type e} {State : Type s}
  {M : InstructionModel D Φ (Tree Events)} {policy : Handler State Events}

local notation "prod" => ProductModel.productEquiv (D := D)

namespace Program

variable {A B C K : τ}

theorem run_fst (a : D A) (b : D B) :
    (fst (Φ := Φ) A B).run M ((prod A B).symm (a, b)) = pure a :=
  TensorProofs.run_fst a b

theorem run_snd (a : D A) (b : D B) :
    (snd (Φ := Φ) A B).run M ((prod A B).symm (a, b)) = pure b :=
  TensorProofs.run_snd a b

theorem run_pair (p : Program Φ A B) (q : Program Φ A C) (a : D A) :
    (p.pair q).run M a =
      (p.run M a >>= fun b => q.run M a >>= fun c => pure ((prod B C).symm (b, c))) :=
  TensorProofs.run_pair p q a

theorem run_whiskerLeft (p : Program Φ A B) (k : D K) (a : D A) :
    (p.whiskerLeft K).run M ((prod K A).symm (k, a)) =
      (p.run M a >>= fun b => pure ((prod K B).symm (k, b))) :=
  TensorProofs.run_left p k a

theorem run_whiskerRight (p : Program Φ A B) (a : D A) (k : D K) :
    (p.whiskerRight K).run M ((prod A K).symm (a, k)) =
      (p.run M a >>= fun b => pure ((prod B K).symm (b, k))) :=
  TensorProofs.run_right p a k

/-- The left whiskering changes only the return, retaining exactly the
left input. The exchanges replay from the original handler state. -/
theorem handledTrace_whiskerLeft_iff (p : Program Φ A B) (k : D K) (a : D A)
    (state : State) (trace : Trace Events (D (product K B))) :
    HandledTrace policy state ((p.whiskerLeft K).run M ((prod K A).symm (k, a))) trace ↔
      ∃ original, HandledTrace policy state (p.run M a) original ∧
        original.map (fun b => (prod K B).symm (k, b)) = trace := by
  rw [run_whiskerLeft]
  exact TensorProofs.handled_map_iff _ _ _ _

/-- The right whiskering changes only the return, retaining exactly the
right input. The exchanges replay from the original handler state. -/
theorem handledTrace_whiskerRight_iff (p : Program Φ A B) (a : D A) (k : D K)
    (state : State) (trace : Trace Events (D (product B K))) :
    HandledTrace policy state ((p.whiskerRight K).run M ((prod A K).symm (a, k))) trace ↔
      ∃ original, HandledTrace policy state (p.run M a) original ∧
        original.map (fun b => (prod B K).symm (b, k)) = trace := by
  rw [run_whiskerRight]
  exact TensorProofs.handled_map_iff _ _ _ _

end Program

namespace Arrow

variable {A B : Interface M policy}

/-- Fix the left object and act on the right arrow. -/
def whiskerLeft (K : Interface M policy) (f : A ⟶ B) : K.tensor A ⟶ K.tensor B :=
  Quotient.map' (Program.whiskerLeft K.ty)
    (by
      intro _ _ h
      exact ⟨TensorProofs.left_mono _ h.1, TensorProofs.left_mono _ h.2⟩) f

/-- Fix the right object and act on the left arrow. -/
def whiskerRight (f : A ⟶ B) (K : Interface M policy) : A.tensor K ⟶ B.tensor K :=
  Quotient.map' (fun p => Program.whiskerRight p K.ty)
    (by
      intro _ _ h
      exact ⟨TensorProofs.right_mono _ h.1, TensorProofs.right_mono _ h.2⟩) f

@[simp] theorem whiskerLeft_ofProgram (K : Interface M policy) (p : Program Φ A.ty B.ty) :
    whiskerLeft K (ofProgram (A := A) (B := B) p) = ofProgram (p.whiskerLeft K.ty) :=
  rfl

@[simp] theorem whiskerRight_ofProgram (p : Program Φ A.ty B.ty) (K : Interface M policy) :
    whiskerRight (ofProgram (A := A) (B := B) p) K = ofProgram (p.whiskerRight K.ty) :=
  rfl

theorem whiskerLeft_mono (K : Interface M policy) :
    Monotone (whiskerLeft K : (A ⟶ B) → (K.tensor A ⟶ K.tensor B)) :=
  fun f g => Quotient.inductionOn₂ f g fun _ _ => TensorProofs.left_mono K.ty

theorem whiskerRight_mono (K : Interface M policy) :
    Monotone (fun f : A ⟶ B => whiskerRight f K) :=
  fun f g => Quotient.inductionOn₂ f g fun _ _ => TensorProofs.right_mono K.ty

end Arrow

/-- The fixed-left action is a functor on the native program category. -/
def tensorLeft (K : Interface M policy) : Interface M policy ⥤ Interface M policy where
  obj := K.tensor
  map := Arrow.whiskerLeft K
  map_id _ := by exact Quotient.sound (TensorProofs.left_id _ _)
  map_comp f g := by
    exact Quotient.inductionOn₂ f g fun p q => Quotient.sound (TensorProofs.left_seq K.ty p q)

/-- The fixed-right action is a functor on the native program category. -/
def tensorRight (K : Interface M policy) : Interface M policy ⥤ Interface M policy where
  obj A := A.tensor K
  map f := Arrow.whiskerRight f K
  map_id _ := by exact Quotient.sound (TensorProofs.right_id _ _)
  map_comp f g := by
    exact Quotient.inductionOn₂ f g fun p q => Quotient.sound (TensorProofs.right_seq K.ty p q)

theorem tensorLeft_enriched (K : Interface M policy) : EnrichedFunctor (tensorLeft K) :=
  fun h => Arrow.whiskerLeft_mono K h

theorem tensorRight_enriched (K : Interface M policy) : EnrichedFunctor (tensorRight K) :=
  fun h => Arrow.whiskerRight_mono K h

end Silmaril.Isotope.LetCase.HandledTrace
