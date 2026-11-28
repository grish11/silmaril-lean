module

public import Silmaril.SSA.Isotope.Institution.Thms
public import Silmaril.Semantics.NondeterministicTrace.Thms
public import Mathlib.Algebra.FreeMonoid.Basic

/-! # Native LetSeq terms with ordered pair requests and atomic projections -/

@[expose] public section

namespace Silmaril.Isotope.LetSeq.StraightLine

open LocallyNameless (Derivation Equiv Pure Tm)
open Silmaril.Isotope.Semantics (BoundEnv InstructionModel)
open Silmaril.Semantics.NondeterministicTrace

abbrev Types := Ty Unit
abbrev Atom : Types := .base ()
abbrev Packet : Types := .product Atom Atom

/-- Distinct requests with a common pair interface. -/
inductive Request where
  | ask (label : Bool)

instance : HasTy Request Types := ⟨fun _ => Packet, fun _ => Packet⟩
instance : HasEff Request Bool := ⟨fun _ => true⟩

abbrev Term := Tm Empty Request
abbrev Γ₀ : Ctx Empty Types := .nil

abbrev Value := Ty.denote (fun _ : Unit => Nat)

/-- A recorded request includes its actual argument and reply coordinates. -/
structure Event where
  request : Request
  argument : Nat × Nat
  reply : Nat × Nat

abbrev Log := FreeMonoid Event
abbrev Trace := Silmaril.Semantics.NondeterministicTrace.Finite Log

def model : InstructionModel Value Request Trace where
  eval f x := Finite.ofOutcomes (Set.range fun y : Nat × Nat => (y, FreeMonoid.of ⟨f, x, y⟩))

def run {n : Nat} {β : BoundCtx Types n} {t : Term n} {A : Types}
    (d : Derivation Request Γ₀ β t A) (ρ : BoundEnv Value β) : Trace (Value A) :=
  d.denote Value model (fun x => x.elim) ρ

/-- A retained variable at the atomic sort, possibly below a packet binder. -/
abbrev Slot {n : Nat} (β : BoundCtx Types n) := {i : Fin n // β.get i = Atom}

def Slot.value {n : Nat} {β : BoundCtx Types n} (s : Slot β) (ρ : BoundEnv Value β) : Nat :=
  cast (congrArg Value s.2) (ρ s.1)

def requestTerm {n : Nat} (f : Request) (x y : Fin n) : Term n :=
  .op f (.pair (.bv x) (.bv y))

/-- Native straight-line terms. Each request binds the left reply then
the right reply. A packet binder may precede destructuring, and an atomic
return may use an explicit pure alias. -/
inductive Admitted : {n : Nat} → (β : BoundCtx Types n) → Term n → Type where
  | ret {n : Nat} {β : BoundCtx Types n} (x : Slot β) :
      Admitted β (.bv x.1)
  | aliasReturn {n : Nat} {β : BoundCtx Types n} (x : Slot β) :
      Admitted β (.let₁ (.bv x.1) (.bv 0))
  | request {n : Nat} {β : BoundCtx Types n} {body : Term (n + 2)}
      (f : Request) (x y : Slot β) (rest : Admitted ((β.snoc Atom).snoc Atom) body) :
      Admitted β (.let₂ (requestTerm f x.1 y.1) body)
  | bound {n : Nat} {β : BoundCtx Types n} {body : Term (n + 2)}
      (f : Request) (x y : Slot β) (rest : Admitted ((β.snoc Atom).snoc Atom) body) :
      Admitted β (.let₁ (requestTerm f x.1 y.1) (.let₂ (.bv 0) body.underTwoBinders))

/-- A fully assembled pure value of structural type, with atom leaves drawn
from the retained projections. -/
inductive Assembly {n : Nat} (β : BoundCtx Types n) : Types → Type where
  | slot (i : Slot β) : Assembly β Atom
  | unit : Assembly β .unit
  | pair {A B : Types} (a : Assembly β A) (b : Assembly β B) : Assembly β (.product A B)

def Assembly.term {n : Nat} {β : BoundCtx Types n} {A : Types} : Assembly β A → Term n
  | .slot i => .bv i.1
  | .unit => .unit
  | .pair a b => .pair a.term b.term

def Assembly.value {n : Nat} {β : BoundCtx Types n} {A : Types}
    (ρ : BoundEnv Value β) : Assembly β A → Value A
  | .slot i => i.value ρ
  | .unit => ⟨⟩
  | .pair a b => (a.value ρ, b.value ρ)

/-- A substitution from the variables of a native pure derivation to
assemblies over the currently retained atomic slots. -/
abbrev AssemblyEnv {n m : Nat} (source : BoundCtx Types n) (target : BoundCtx Types m) :=
  (i : Fin n) → Assembly target (source.get i)

def AssemblyEnv.terms {n m : Nat} {source : BoundCtx Types n} {target : BoundCtx Types m}
    (σ : AssemblyEnv source target) (i : Fin n) : Term m :=
  (σ i).term

/-- An argument or result is an assembly, or a native pure term on assembled
inputs. The latter admits native unit, products, projections and pure lets at
arbitrary depth. -/
inductive PureAssembly : {n : Nat} → BoundCtx Types n → Term n → Types → Type where
  | assembled {n : Nat} {β : BoundCtx Types n} {A : Types} (v : Assembly β A) :
      PureAssembly β v.term A
  | substituted {n m : Nat} {source : BoundCtx Types n} {target : BoundCtx Types m}
      {t : Term n} {A : Types} (d : Derivation Request Γ₀ source t A) (h : Pure false t)
      (σ : AssemblyEnv source target) : PureAssembly target (t.bsubst σ.terms) A

/-- Straight-line requests with pure arguments and structural results. -/
inductive ProductProgram : {n : Nat} → BoundCtx Types n → Term n → Types → Type where
  | ret {n : Nat} {β : BoundCtx Types n} {t : Term n} {A : Types} (v : PureAssembly β t A) :
      ProductProgram β t A
  | request {n : Nat} {β : BoundCtx Types n} {arg : Term n} {body : Term (n + 2)} {A : Types}
      (f : Request) (a : PureAssembly β arg Packet)
      (rest : ProductProgram ((β.snoc Atom).snoc Atom) body A) :
      ProductProgram β (.let₂ (.op f arg) body) A
  | bound {n : Nat} {β : BoundCtx Types n} {arg : Term n} {body : Term (n + 2)} {A : Types}
      (f : Request) (a : PureAssembly β arg Packet)
      (rest : ProductProgram ((β.snoc Atom).snoc Atom) body A) :
      ProductProgram β (.let₁ (.op f arg) (.let₂ (.bv 0) body.underTwoBinders)) A

/-- The original atomic fragment is a subfragment on the same native terms. -/
def Admitted.toProduct {n : Nat} {β : BoundCtx Types n} {t : Term n} :
    Admitted β t → ProductProgram β t Atom
  | .ret x => .ret (.assembled (.slot x))
  | .aliasReturn x =>
    .ret (.substituted
      (.let₁ .bv .bv : Derivation Request Γ₀ (.snoc .nil Atom) (.let₁ (.bv 0) (.bv 0)) Atom)
      (.let₁ .bv .bv) (Fin.cases (.slot x) (fun i => i.elim0)))
  | .request f x y rest => .request f (.assembled (.pair (.slot x) (.slot y))) rest.toProduct
  | .bound f x y rest => .bound f (.assembled (.pair (.slot x) (.slot y))) rest.toProduct

/-- The normal forms use direct packet destructuring and pure assembled values. -/
inductive ProductCanonical : {n : Nat} → BoundCtx Types n → Term n → Types → Type where
  | result {n : Nat} {β : BoundCtx Types n} {A : Types} (v : Assembly β A) :
      ProductCanonical β v.term A
  | step {n : Nat} {β : BoundCtx Types n} {A : Types} {body : Term (n + 2)}
      (f : Request) (arg : Assembly β Packet)
      (rest : ProductCanonical ((β.snoc Atom).snoc Atom) body A) :
      ProductCanonical β (.let₂ (.op f arg.term) body) A

def ProductCanonical.toProgram {n : Nat} {β : BoundCtx Types n} {t : Term n} {A : Types} :
    ProductCanonical β t A → ProductProgram β t A
  | .result v => .ret (.assembled v)
  | .step f arg rest => .request f (.assembled arg) rest.toProgram

/-- Native equivalence to a canonical member of the structural program grammar. -/
def ProductNormalizes {n : Nat} (β : BoundCtx Types n) (t : Term n) (A : Types) : Prop :=
  ∃ u : Term n, ∃ _ : ProductCanonical β u A, Equiv false Γ₀ β t u A

/-- The original atomic normal forms, with direct packet destructuring. -/
inductive Canonical : {n : Nat} → (β : BoundCtx Types n) → Term n → Type where
  | ret {n : Nat} {β : BoundCtx Types n} (x : Slot β) :
      Canonical β (.bv x.1)
  | request {n : Nat} {β : BoundCtx Types n} {body : Term (n + 2)}
      (f : Request) (x y : Slot β) (rest : Canonical ((β.snoc Atom).snoc Atom) body) :
      Canonical β (.let₂ (requestTerm f x.1 y.1) body)

def Canonical.toProduct {n : Nat} {β : BoundCtx Types n} {t : Term n} :
    Canonical β t → ProductCanonical β t Atom
  | .ret x => .result (.slot x)
  | .request f x y rest => .step f (.pair (.slot x) (.slot y)) rest.toProduct

def Admitted.normal {n : Nat} {β : BoundCtx Types n} {t : Term n} :
    Admitted β t → Term n
  | .ret x | .aliasReturn x => .bv x.1
  | .request f x y rest | .bound f x y rest =>
    .let₂ (requestTerm f x.1 y.1) rest.normal

def slotDerivation {n : Nat} {β : BoundCtx Types n} (x : Slot β) :
    Derivation Request Γ₀ β (.bv x.1) Atom :=
  cast (congrArg (Derivation Request Γ₀ β (.bv x.1)) x.2) .bv

def requestDerivation {n : Nat} {β : BoundCtx Types n} (f : Request) (x y : Slot β) :
    Derivation Request Γ₀ β (requestTerm f x.1 y.1) Packet :=
  .op (.pair (slotDerivation x) (slotDerivation y))

def Assembly.derivation {n : Nat} {β : BoundCtx Types n} {A : Types}
    (v : Assembly β A) : Derivation Request Γ₀ β v.term A :=
  match v with
  | .slot i => slotDerivation i
  | .unit => .unit
  | .pair a b => .pair a.derivation b.derivation

def ProductCanonical.derivation {n : Nat} {β : BoundCtx Types n} {t : Term n} {A : Types} :
    ProductCanonical β t A → Derivation Request Γ₀ β t A
  | .result v => v.derivation
  | .step f arg rest => .let₂ (.op (f := f) arg.derivation) rest.derivation

def canonicalDerivation {n : Nat} {β : BoundCtx Types n} {t : Term n}
    (w : Canonical β t) : Derivation Request Γ₀ β t Atom :=
  w.toProduct.derivation

def normalWitness {n : Nat} {β : BoundCtx Types n} {t : Term n}
    (w : Admitted β t) : Canonical β w.normal :=
  match w with
  | .ret i | .aliasReturn i => .ret i
  | .request f x y rest | .bound f x y rest => .request f x y (normalWitness rest)

/-- The atom slots carry distinct atoms below a supply for fresh replies. -/
structure Separating {n : Nat} {β : BoundCtx Types n} (ρ : BoundEnv Value β) (fresh : Nat) : Prop where
  injective : Function.Injective (fun s : Slot β => s.value ρ)
  below : ∀ s : Slot β, s.value ρ < fresh

/-- Every input supplied to the open packet program is a native product. -/
abbrev input : BoundCtx Types 1 := .snoc .nil Packet

def packetEnv (pair : Nat × Nat) : BoundEnv Value input :=
  BoundEnv.snoc (β := .nil) (A := Packet) (fun i => i.elim0) pair

/-- The entry explicitly projects the two components of that native input. -/
def entry {body : Term 3} {A : Types}
    (d : Derivation Request Γ₀ ((input.snoc Atom).snoc Atom) body A) :
    Derivation Request Γ₀ input (.let₂ (.bv 0) body) A :=
  .let₂ .bv d

end Silmaril.Isotope.LetSeq.StraightLine
