module

public import Silmaril.Logic.Algebraic.Lambda.Semantics
public import Silmaril.Logic.STLCMatching.Signatures

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Algebraic.Lambda
open CategoryTheory Silmaril.Logic.Institution.Examples
open Silmaril.Calculi.TypedLambda Silmaril.Calculi.LambdaCube
open Cslib.LambdaCalculus.LocallyNameless.Stlc

/-- Actual EQ signatures with fixed sorts; arbitrary operator maps remain. -/
structure FixedSignature (B : Type) where
  operations : (n : Nat) → (Fin n → B) → B → Type

abbrev FixedSignature.equational {B : Type} (A : FixedSignature B) : EQ.Signature :=
  ⟨B, A.operations⟩

structure FixedHom {B : Type} (A D : FixedSignature B) where
  operations : ∀ {n w s}, A.operations n w s → D.operations n w s

instance {B : Type} : Category (FixedSignature B) where
  Hom := FixedHom
  id _ := ⟨fun o => o⟩
  comp f g := ⟨fun o => g.operations (f.operations o)⟩

def FixedHom.equational {B : Type} {A D : FixedSignature B} (f : A ⟶ D) :
    A.equational ⟶ D.equational := ⟨id, f.operations⟩

def toEquational (B : Type) : FixedSignature B ⥤ EQ.Signature where
  obj := FixedSignature.equational
  map := FixedHom.equational

abbrev FixedSignature.lambda {B : Type} (A : FixedSignature B) : STLCMatching.FixedSignature B :=
  ⟨Operation A.equational⟩

def FixedHom.operation {B : Type} {A D : FixedSignature B} (f : A ⟶ D) :
    {as : List (Ty B)} → {τ : Ty B} → Operation A.equational as τ → Operation D.equational as τ
  | _, _, .original o => .original (f.operations o)

def FixedHom.lambda {B : Type} {A D : FixedSignature B} (f : A ⟶ D) :
    A.lambda ⟶ D.lambda := ⟨f.operation⟩

theorem operation_id {B : Type} (A : FixedSignature B) {as τ} (o : Operation A.equational as τ) :
    FixedHom.operation (𝟙 A) o = o :=
  Operation.rec (motive := fun _as _τ o => FixedHom.operation (𝟙 A) o = o) (fun _ => rfl) o

theorem operation_comp {B : Type} {A D E : FixedSignature B} (f : A ⟶ D) (g : D ⟶ E)
    {as τ} (o : Operation A.equational as τ) :
    FixedHom.operation (f ≫ g) o = g.operation (f.operation o) :=
  Operation.rec (motive := fun _as _τ o =>
    FixedHom.operation (f ≫ g) o = g.operation (f.operation o)) (fun _ => rfl) o

def toLambda (B : Type) : FixedSignature B ⥤ STLCMatching.FixedSignature B where
  obj := FixedSignature.lambda
  map := FixedHom.lambda
  map_id A := congrArg STLCMatching.FixedHom.mk (funext fun _as => funext fun _τ =>
    funext fun o => operation_id A o)
  map_comp f g := congrArg STLCMatching.FixedHom.mk (funext fun _as => funext fun _τ =>
    funext fun o => operation_comp f g o)

theorem term_naturality {B : Type} {A D : FixedSignature B} (f : A ⟶ D)
    {n : Nat} {Γ : Fin n → B} {s : B} (t : EQ.Term A.equational Γ s) :
    (term t).mapOp f.lambda.operators = term (t.map f.equational) := by
  refine EQ.Term.rec (motive := fun s t =>
    (term t).mapOp f.lambda.operators = term (t.map f.equational))
    (fun i => rfl) (fun o args ih => ?_) t
  simp only [term, Term.mapOp, EQ.Term.map, FixedHom.equational, FixedHom.lambda, FixedHom.operation]
  congr 1
  rw [envTuple_map]
  exact congrArg (envTuple _ _) (funext ih)

theorem equation_naturality {B : Type} {A D : FixedSignature B} (f : A ⟶ D)
    (e : EQ.Equation A.equational) :
    STLCMatching.FixedHom.sentence f.lambda (equation e) =
      equation (e.map f.equational) := by
  cases e
  simp only [equation, STLCMatching.FixedHom.sentence, EQ.Equation.map, term_naturality]
  rfl

end Silmaril.Logic.Algebraic.Lambda
