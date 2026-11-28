module

public import Silmaril.SSA.Isotope.LetSeq.StraightLine.Defs

/-! # Exact LetSeq over structural primitive signatures -/

@[expose] public section

namespace Silmaril.Isotope.LetSeq.StraightLine.Structural

open LocallyNameless (Derivation Equiv Tm)
open Silmaril.Isotope.Semantics (BoundEnv InstructionModel)
open Silmaril.Semantics.NondeterministicTrace

/-- Generator interfaces contain only atoms, unit and ordered products. -/
inductive Shape (α : Type) where
  | atom (a : α)
  | unit
  | pair (left right : Shape α)

def Shape.ty {α : Type} : Shape α → Ty α
  | .atom a => .base a
  | .unit => .unit
  | .pair a b => .product a.ty b.ty

class Signature (α Φ : Type) where
  argument : Φ → Shape α
  reply : Φ → Shape α

scoped instance {α Φ : Type} [Signature α Φ] : HasTy Φ (Ty α) :=
  ⟨fun f => (Signature.argument f).ty, fun f => (Signature.reply f).ty⟩

scoped instance {Φ : Type} : HasEff Φ Bool := ⟨fun _ => true⟩

abbrev Term (Φ : Type) := Tm Empty Φ
abbrev Context (α : Type) := BoundCtx (Ty α)
abbrev Γ₀ {α : Type} : Ctx Empty (Ty α) := .nil

abbrev Value {α : Type} := Ty.denote (fun _ : α => Nat)
abbrev Slot {α : Type} {n : Nat} (β : Context α n) (A : Ty α) := {i : Fin n // β.get i = A}

def Slot.rename {α : Type} {n m : Nat} {β : Context α n} {γ : Context α m} {A : Ty α}
    (ρ : BoundCtx.Renaming β γ) (s : Slot β A) : Slot γ A :=
  ⟨ρ.toFun s.1, (ρ.typed s.1).trans s.2⟩

def Slot.value {α : Type} {n : Nat} {β : Context α n} {A : Ty α}
    (s : Slot β A) (ρ : BoundEnv Value β) : Value A :=
  cast (congrArg Value s.2) (ρ s.1)

def Slot.derivation {α Φ : Type} [Signature α Φ] {n : Nat} {β : Context α n} {A : Ty α}
    (s : Slot β A) : Derivation Φ Γ₀ β (.bv s.1) A :=
  cast (congrArg (Derivation Φ Γ₀ β (.bv s.1)) s.2) .bv

/-- Normal pure terms contain only structural constructors and atom slots. -/
inductive Assembly {α : Type} {n : Nat} (β : Context α n) : Ty α → Type where
  | atom {a : α} (s : Slot β (.base a)) : Assembly β (.base a)
  | unit : Assembly β .unit
  | pair {A B : Ty α} (a : Assembly β A) (b : Assembly β B) : Assembly β (.product A B)

def Assembly.term {α Φ : Type} {n : Nat} {β : Context α n} {A : Ty α} :
    Assembly β A → Term Φ n
  | .atom i => .bv i.1
  | .unit => .unit
  | .pair a b => .pair a.term b.term

def Assembly.rename {α : Type} {n m : Nat} {β : Context α n} {γ : Context α m} {A : Ty α}
    (ρ : BoundCtx.Renaming β γ) : Assembly β A → Assembly γ A
  | .atom i => .atom (i.rename ρ)
  | .unit => .unit
  | .pair a b => .pair (a.rename ρ) (b.rename ρ)

def Assembly.derivation {α Φ : Type} [Signature α Φ] {n : Nat} {β : Context α n} {A : Ty α}
    (v : Assembly β A) : Derivation Φ Γ₀ β v.term A :=
  match v with
  | .atom i => i.derivation
  | .unit => .unit
  | .pair a b => .pair a.derivation b.derivation

def Assembly.value {α : Type} {n : Nat} {β : Context α n} {A : Ty α}
    (ρ : BoundEnv Value β) : Assembly β A → Value A
  | .atom i => i.value ρ
  | .unit => ⟨⟩
  | .pair a b => (a.value ρ, b.value ρ)

abbrev AssemblyEnv {α : Type} {n m : Nat} (source : Context α n) (target : Context α m) :=
  (i : Fin n) → Assembly target (source.get i)

def AssemblyEnv.terms {α Φ : Type} {n m : Nat} {source : Context α n} {target : Context α m}
    (σ : AssemblyEnv source target) : Fin n → Term Φ m :=
  fun i => (σ i).term

def AssemblyEnv.extend {α : Type} {n m : Nat} {source : Context α n} {target : Context α m}
    {A : Ty α} (σ : AssemblyEnv source target) (v : Assembly target A) :
    AssemblyEnv (source.snoc A) target :=
  Fin.cases v σ

def AssemblyEnv.rename {α : Type} {n m k : Nat} {source : Context α n} {target : Context α m}
    {γ : Context α k} (σ : AssemblyEnv source target) (ρ : BoundCtx.Renaming target γ) :
    AssemblyEnv source γ :=
  fun i => (σ i).rename ρ

/-- Pure product destructuring in a native context. Each step opens an
existing slot. New slots remain in scope for the following steps. -/
inductive Split {α : Type} : {n m : Nat} → Context α n → Context α m → Type where
  | nil {n : Nat} {β : Context α n} : Split β β
  | pair {n m : Nat} {β : Context α n} {γ : Context α m} {A B : Ty α}
      (s : Slot β (.product A B)) (next : Split ((β.snoc A).snoc B) γ) : Split β γ

def Split.rename {α : Type} {n m : Nat} {β : Context α n} {γ : Context α m} :
    Split β γ → BoundCtx.Renaming β γ
  | .nil => .id _
  | .pair (A := A) (B := B) _ next =>
    ((BoundCtx.Renaming.succ β A).comp (BoundCtx.Renaming.succ (β.snoc A) B)).comp next.rename

def Split.wrap {α Φ : Type} {n m : Nat} {β : Context α n} {γ : Context α m} :
    Split β γ → Term Φ m → Term Φ n
  | .nil, t => t
  | .pair s next, t => .let₂ (.bv s.1) (next.wrap t)

def Split.append {α : Type} {n m k : Nat}
    {β : Context α n} {γ : Context α m} {δ : Context α k} :
    Split β γ → Split γ δ → Split β δ
  | .nil, q => q
  | .pair s p, q => .pair s (p.append q)

def Split.derivation {α Φ : Type} [Signature α Φ] {n m : Nat} {β : Context α n} {γ : Context α m} {t : Term Φ m} {A : Ty α} :
    (p : Split β γ) → Derivation Φ Γ₀ γ t A → Derivation Φ Γ₀ β (p.wrap t) A
  | .nil, d => d
  | .pair s next, d => .let₂ s.derivation (next.derivation d)

def Split.env {α : Type} {n m : Nat} {β : Context α n} {γ : Context α m} :
    Split β γ → BoundEnv Value β → BoundEnv Value γ
  | .nil, ρ => ρ
  | .pair slot next, ρ =>
    let ab := slot.value ρ
    next.env ((ρ.snoc ab.1).snoc ab.2)

structure Unpacked {α : Type} {n : Nat} (β : Context α n) (A : Ty α) where
  size : Nat
  context : Context α size
  split : Split β context
  value : Assembly context A

/-- Expose the atom leaves of a structural slot in deterministic left-to-right order. -/
def Shape.unpack {α : Type} {n : Nat} {β : Context α n} :
    (s : Shape α) → Slot β s.ty → Unpacked β s.ty
  | .atom _, slot => ⟨_, β, .nil, .atom slot⟩
  | .unit, _ => ⟨_, β, .nil, .unit⟩
  | .pair a b, slot =>
    let l := a.unpack (β := (β.snoc a.ty).snoc b.ty) ⟨1, rfl⟩
    let r := b.unpack (Slot.rename l.split.rename ⟨0, rfl⟩)
    ⟨_, r.context, .pair slot (l.split.append r.split), .pair (l.value.rename r.split.rename) r.value⟩

def replyUnpack {α Φ : Type} [Signature α Φ] {n : Nat} (β : Context α n) (f : Φ) :
    Unpacked (β.snoc (instrTrg f)) (instrTrg f) :=
  (Signature.reply f).unpack ⟨0, rfl⟩

/-- Requests bind the whole reply once. Only pure native destructuring
follows before the next request and the eventual assembly result. -/
inductive Normal {α Φ : Type} [Signature α Φ] :
    {n : Nat} → (β : Context α n) → Term Φ n → Ty α → Type where
  | ret {n : Nat} {β : Context α n} {A : Ty α} (a : Assembly β A) : Normal β a.term A
  | request {n : Nat} {β : Context α n} {A : Ty α}
      (f : Φ) (a : Assembly β (instrSrc f)) {t : Term Φ (replyUnpack β f).size}
      (next : Normal (replyUnpack β f).context t A) :
      Normal β (.let₁ (.op f a.term) ((replyUnpack β f).split.wrap t)) A

def Normal.derivation {α Φ : Type} [Signature α Φ] {n : Nat} {β : Context α n}
    {t : Term Φ n} {A : Ty α} : Normal β t A → Derivation Φ Γ₀ β t A
  | .ret v => v.derivation
  | .request f a p => .let₁ (.op (f := f) a.derivation) ((replyUnpack β f).split.derivation p.derivation)

def Normalizes {α Φ : Type} [Signature α Φ] {n : Nat}
    (β : Context α n) (t : Term Φ n) (A : Ty α) : Prop :=
  ∃ u : Term Φ n, ∃ _ : Normal β u A, Equiv false Γ₀ β t u A

def Shape.leaves {α : Type} : Shape α → Nat
  | .atom _ => 1
  | .unit => 0
  | .pair a b => a.leaves + b.leaves

def Shape.fresh {α : Type} : (s : Shape α) → Nat → Value s.ty
  | .atom _, k => k
  | .unit, _ => ⟨⟩
  | .pair a b, k => (a.fresh k, b.fresh (k + a.leaves))

/-- The ordered right-associated product of a finite list of input types. -/
def Shape.pack {α : Type} : List (Shape α) → Shape α
  | [] => .unit
  | x :: xs => .pair x (Shape.pack xs)

abbrev Packed {α : Type} (s : Shape α) : Context α 1 := .snoc .nil s.ty

def packedUnpack {α : Type} (s : Shape α) : Unpacked (Packed s) s.ty :=
  s.unpack ⟨0, rfl⟩

def packedEnv {α : Type} (s : Shape α) (x : Value s.ty) : BoundEnv Value (Packed s) :=
  BoundEnv.snoc (β := .nil) (fun i => i.elim0) x

/-- The slots of each atom sort are distinct and their tokens belong to the
allocated set. Products in the context do not count as exposed atoms. -/
structure Separates {α : Type} {n : Nat} {β : Context α n} (ρ : BoundEnv Value β) (used : Set Nat) : Prop where
  injective (a : α) : Function.Injective (fun s : Slot β (.base a) => s.value ρ)
  allocated (a : α) (s : Slot β (.base a)) : s.value ρ ∈ used

/-- The event carries values at the actual argument and reply types of its generator. -/
structure Event {α Φ : Type} [HasTy Φ (Ty α)] where
  generator : Φ
  argument : Value (instrSrc (τ := Ty α) generator)
  reply : Value (instrTrg (τ := Ty α) generator)

abbrev Log (α Φ : Type) [HasTy Φ (Ty α)] := FreeMonoid (Event (α := α) (Φ := Φ))
abbrev Trace (α Φ : Type) [HasTy Φ (Ty α)] := Silmaril.Semantics.NondeterministicTrace.Finite (Log α Φ)

def model {α Φ : Type} [HasTy Φ (Ty α)] : InstructionModel (Value (α := α)) Φ (Trace α Φ) where
  eval f x := Finite.ofOutcomes (Set.range fun y : Value (instrTrg f) => (y, FreeMonoid.of ⟨f, x, y⟩))

def run {α Φ : Type} [Signature α Φ] {n : Nat} {β : Context α n} {t : Term Φ n} {A : Ty α}
    (d : Derivation Φ Γ₀ β t A) (ρ : BoundEnv Value β) : Trace α Φ (Value A) :=
  d.denote Value model (fun x => x.elim) ρ

end Silmaril.Isotope.LetSeq.StraightLine.Structural
