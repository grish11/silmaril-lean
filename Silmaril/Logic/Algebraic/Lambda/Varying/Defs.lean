module

public import Silmaril.Logic.STLCEquations.Institution

/-! The first-order equation compiler on the full public EQ signature category.
Sort maps may identify types. Actual typed terms and full-function set models
are reused; raw typing assertions are outside the target sentence language. -/
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Algebraic.Lambda.Varying
open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Examples
open Silmaril.Calculi.TypedLambda Silmaril.Calculi.LambdaCube
open Silmaril.Calculi.LambdaCube.STLC
open Cslib.LambdaCalculus.LocallyNameless.Stlc

abbrev language (A : EQ.Signature) : STLCEquations.Language := ⟨signature A⟩

/-- Mapping sorts changes the variable types without changing their positions. -/
@[simp] theorem context_map {B D : Type} (f : B → D) {n : Nat} (w : Fin n → B) :
    (context w).map (mapTy f) = context (f ∘ w) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (List.cons (.base (f (w 0)))) (ih (fun i => w i.succ))

def mapOperation {A D : EQ.Signature} (f : A ⟶ D) :
    {as : List (Ty A.S)} → {τ : Ty A.S} → Operation A as τ →
      Operation D (as.map (mapTy f.sorts)) (mapTy f.sorts τ)
  | _, _, .original o => by
      simpa only [context_map, mapTy] using Operation.original (f.ops o)

def signatureMap {A D : EQ.Signature} (f : A ⟶ D) :
    STLCEquations.Hom (language A) (language D) := ⟨f.sorts, mapOperation f⟩

def compile {A : EQ.Signature} (e : EQ.Equation A) : STLCEquations.Sentence (language A) :=
  .equation (term e.lhs) (term e.rhs)

end Silmaril.Logic.Algebraic.Lambda.Varying
