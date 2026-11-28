module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.Live.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Typing.Thms

/-! # Typed rows that cannot read the local feedback payload -/

@[expose] public section

universe u v u₁ v₁

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical.UnusedSummand

variable {κ : Type u} {Φ : Type v} [HasTy Φ (Ty κ)]

/-- The expression forms used in a row. Variables refer to the retained
context or a reply bound by a case. Each expression has a determined type. -/
inductive Operand : VCtx (Ty κ) → Ty κ → Type (max u v) where
  | var {Γ A} (i : Nat) (typed : At Γ i A) : Operand Γ A
  | unit {Γ} : Operand Γ Silmaril.unit
  | op {Γ} (p : Φ) (arg : Operand Γ (instrSrc p)) : Operand Γ (instrTrg p)
  | let₁ {Γ A B} (value : Operand Γ A) (body : Operand (A :: Γ) B) : Operand Γ B
  | pair {Γ A B} (left : Operand Γ A) (right : Operand Γ B) : Operand Γ (Silmaril.product A B)
  | let₂ {Γ A B D} (value : Operand Γ (Silmaril.product A B)) (body : Operand (B :: A :: Γ) D) :
      Operand Γ D

def Operand.term {Γ : VCtx (Ty κ)} {A : Ty κ} : Operand (Φ := Φ) Γ A → Tm Φ
  | .var i _ => .var i
  | .unit => .unit
  | .op p arg => .op p arg.term
  | .let₁ value body => .let₁ value.term body.term
  | .pair left right => .pair left.term right.term
  | .let₂ value body => .let₂ value.term body.term

/-- A finite row can evaluate a discriminator, return at an outward label,
or transfer to any local label with its common payload. A let evaluates
its initializer once. A product let binds its right field newest. -/
inductive Row {n : Nat} (R : Fin n → Ty κ) (L : LCtx (Ty κ)) :
    VCtx (Ty κ) → Type (max u v) where
  | jump {Γ} (i : Fin n) (arg : Operand (Φ := Φ) Γ (R i)) : Row R L Γ
  | let₁ {Γ A} (value : Operand (Φ := Φ) Γ A) (body : Row R L (A :: Γ)) : Row R L Γ
  | let₂ {Γ A B} (value : Operand (Φ := Φ) Γ (Silmaril.product A B)) (body : Row R L (B :: A :: Γ)) :
      Row R L Γ
  | exit {Γ A} (i : Nat) (target : At L i A) (arg : Operand (Φ := Φ) Γ A) : Row R L Γ
  | case {Γ A B} (arg : Operand (Φ := Φ) Γ (Silmaril.coprod A B))
      (left : Row R L (A :: Γ)) (right : Row R L (B :: Γ)) : Row R L Γ

/-- A tail assignment widens every local payload on the right. -/
def family {n : Nat} (R : Fin n → Ty κ) (tails : Option (Fin n → Ty κ)) : Fin n → Ty κ :=
  match tails with
  | none => R
  | some D => fun i => Silmaril.coprod (R i) (D i)

/-- The tag is the same for every tail assignment. The input renaming skips
the local CFG binder in block rows and preserves let and case binders. -/
def Row.region {n : Nat} {R : Fin n → Ty κ} {L : LCtx (Ty κ)}
    (tag : Bool) (ρ : Nat → Nat) {Γ : VCtx (Ty κ)} : Row (Φ := Φ) R L Γ → Region Φ
  | .jump i arg => .br i (if tag then .inl (arg.term.rename ρ) else arg.term.rename ρ)
  | .let₁ value body => .let₁ (value.term.rename ρ) (body.region tag (Silmaril.DeBruijn.lift ρ))
  | .let₂ value body => .let₂ (value.term.rename ρ) (body.region tag (Silmaril.DeBruijn.liftN 2 ρ))
  | .exit i _ arg => .br (n + i) (arg.term.rename ρ)
  | .case arg left right => .case (arg.term.rename ρ)
      (left.region tag (Silmaril.DeBruijn.lift ρ)) (right.region tag (Silmaril.DeBruijn.lift ρ))

/-- Each row uses the same retained input context and has all the local and
outward labels available. The local payload variable is outside that context. -/
structure Program {n : Nat} (R : Fin n → Ty κ) (L : LCtx (Ty κ)) (Γ : VCtx (Ty κ)) where
  entry : Row (Φ := Φ) R L Γ
  blocks : Fin n → Row (Φ := Φ) R L Γ

/-- All widened families give the very same raw region. -/
def Program.region {n : Nat} {R : Fin n → Ty κ} {L : LCtx (Ty κ)} {Γ : VCtx (Ty κ)}
    (p : Program (Φ := Φ) R L Γ) (tag : Bool) : Region Φ :=
  .cfg (p.entry.region tag id) n (fun i => (p.blocks i).region tag Nat.succ)

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel)

/-- The value map keeps the local label index and injects its payload into
the left summand at that label. -/
noncomputable def embedLabels {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V]
    [HasFiniteCoproducts V] (M : TypeModel (Ty κ) V) {n : Nat} (R D : Fin n → Ty κ) :
    labelObj M (List.ofFn R) ⟶ labelObj M (List.ofFn (family R (some D))) :=
  labelObjToFinite M R ≫ Sigma.desc fun i =>
    (CategoryTheory.Limits.coprod.inl ≫ (M.coprodIso (R i) (D i)).inv : M.obj (R i) ⟶ M.obj (family R (some D) i)) ≫
      labelInject M (L := List.ofFn (family R (some D))) i (by simp [At])

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical.UnusedSummand
