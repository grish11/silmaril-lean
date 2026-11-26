module

public import Silmaril.SSA.Isotope.LetCase.Structural.Reply.Thms

/-! # Constructor inputs and reply heads for finite native LetCase -/

@[expose] public section

namespace Silmaril.Isotope.LetCase.Structural.Finite

open LocallyNameless (Derivation Equiv Tm)
open Reply (Γ₀)
open scoped LetSeq.StraightLine.Structural

abbrev Types := Ty Empty
abbrev Term (Φ : Type) := Tm Empty Φ
abbrev Context (n : Nat) := BoundCtx Types n

/-- The admissible primitive interfaces are inhabited by construction. -/
inductive Shape where
  | unit
  | pair (left right : Shape)
  | sum (left right : Shape)

def Shape.ty : Shape → Types
  | .unit => .unit
  | .pair a b => .product a.ty b.ty
  | .sum a b => .coprod a.ty b.ty

class Signature (Φ : Type) where
  source : Φ → Shape
  target : Φ → Shape

scoped instance {Φ : Type} [Signature Φ] : HasTy Φ Types :=
  ⟨fun f => (Signature.source f).ty, fun f => (Signature.target f).ty⟩

/-- Typed closed values of the native constructor language. -/
inductive Constructor : Types → Type where
  | unit : Constructor .unit
  | pair {A B : Types} : Constructor A → Constructor B → Constructor (.product A B)
  | inl {A B : Types} : Constructor A → Constructor (.coprod A B)
  | inr {A B : Types} : Constructor B → Constructor (.coprod A B)

def Shape.witness : (s : Shape) → Constructor s.ty
  | .unit => .unit
  | .pair a b => .pair a.witness b.witness
  | .sum a _ => .inl a.witness

def Constructor.term {Φ : Type} {n : Nat} {A : Types} : Constructor A → Term Φ n
  | .unit => .unit
  | .pair a b => .pair a.term b.term
  | .inl a => .inl a.term
  | .inr b => .inr b.term

def Constructor.typing {Φ : Type} [Signature Φ] {n : Nat} {β : Context n} {A : Types} :
    (v : Constructor A) → Derivation Φ Γ₀ β v.term A
  | .unit => .unit
  | .pair a b => .pair a.typing b.typing
  | .inl a => .inl a.typing
  | .inr b => .inr b.typing

abbrev Value := LetSeq.StraightLine.Structural.Value (α := Empty)

def Constructor.value {A : Types} : Constructor A → Value A
  | .unit => PUnit.unit
  | .pair a b => (a.value, b.value)
  | .inl a => Sum.inl a.value
  | .inr b => Sum.inr b.value

/-- An open interface whose ordered input slots all have inhabited shapes. -/
inductive StructuralContext : {n : Nat} → Context n → Prop where
  | nil : StructuralContext .nil
  | snoc {n : Nat} {β : Context n} (h : StructuralContext β) (s : Shape) :
      StructuralContext (β.snoc s.ty)

/-- A constructor assignment for every native input slot. -/
abbrev Assignment {n : Nat} (β : Context n) := (i : Fin n) → Constructor (β.get i)

def Assignment.terms {Φ : Type} {n : Nat} {β : Context n} (ρ : Assignment β) : Fin n → Term Φ 0 :=
  fun i => (ρ i).term

def Assignment.snoc {n : Nat} {β : Context n} {A : Types} (ρ : Assignment β) (v : Constructor A) :
    Assignment (β.snoc A) :=
  Fin.cases v ρ

/-- A head denotes an actual native closed term. A request has an exact
open body and a smaller witnessed head for every constructor reply. -/
inductive Head {Φ : Type} [Signature Φ] (A : Types) : Term Φ 0 → Type where
  | ret (v : Constructor A) : Head A v.term
  | request (f : Φ) (argument : Constructor (instrSrc f))
      {body : Term Φ 1} (typed : Derivation Φ Γ₀ (.snoc .nil (instrTrg f)) body A)
      (next : Constructor (instrTrg f) → Term Φ 0)
      (heads : ∀ x, Head A (next x))
      (replay : ∀ x, Equiv false Γ₀ .nil (Tm.instantiate body x.term) (next x) A) :
      Head A (.let₁ (.op f argument.term) body)

def Head.typing {Φ : Type} [Signature Φ] {A : Types} {t : Term Φ 0} :
    Head A t → Derivation Φ Γ₀ .nil t A
  | .ret v => v.typing
  | .request _ arg typed _ _ _ => .let₁ (.op arg.typing) typed

/-- Native replay to a head whose subcomputations are witnessed per reply. -/
def Normalizes {Φ : Type} [Signature Φ] (A : Types) (t : Term Φ 0) : Prop :=
  ∃ u : Term Φ 0, ∃ _ : Head A u, Equiv false Γ₀ .nil t u A

end Silmaril.Isotope.LetCase.Structural.Finite
