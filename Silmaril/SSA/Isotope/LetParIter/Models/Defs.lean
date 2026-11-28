module

public import Silmaril.Semantics.ElgotMonads.Parallel.Thms
public import Silmaril.SSA.Isotope.LetParIter.Interpretation.Defs

/-! # Read-only and nondeterministic dialects of LetParIter -/

@[expose] public section

namespace Silmaril.Isotope.LetParIter.Models

open Parallel (Derivation)
open LetIter.ProofRelevant.Semantics

inductive Atom where
  | number

abbrev Code := Ty Atom
abbrev number : Code := .base .number
abbrev Value := Ty.fold (⟨Prod, Unit, Sum, Empty⟩ : Ty.Algebra Type) (fun _ : Atom => Nat)

/-- Interpret the structural coercions of the dialects' type codes. -/
def coerce {A B : Code} : Ty.Subty A B → Value A → Value B
  | .refl _ => id
  | .trans f g => coerce g ∘ coerce f
  | .product f g => Prod.map (coerce f) (coerce g)
  | .coprod f g => Sum.map (coerce f) (coerce g)
  | .empty _ => Empty.elim
  | .unit _ => fun _ => ()

instance : TypeModel Code where
  interp := Value
  productEquiv A B := _root_.Equiv.refl (Value A × Value B)
  coprodEquiv A B := _root_.Equiv.refl (Value A ⊕ Value B)
  unitEquiv := _root_.Equiv.refl Unit
  emptyEquiv := _root_.Equiv.refl Empty
  coe := coerce

abbrev Closed : Ctx Empty Code := .nil

namespace ReadOnly

/-- The two slots are independently available, and neither read changes them. -/
abbrev Env := Part Nat × Part Nat
abbrev M := ReaderT Env Part
abbrev Effect := Bool × Bool

inductive Instr where
  | readLeft
  | readRight
  | countdown

instance : HasTy Instr Code where
  src
    | .readLeft | .readRight => unit
    | .countdown => number
  trg
    | .readLeft | .readRight => number
    | .countdown => coprod number number

/-- The two non-bottom read effects record distinct coordinates. -/
def effect : Instr → Effect
  | .readLeft => (true, false)
  | .readRight => (false, true)
  | .countdown => (false, false)

instance : HasEff Instr Effect := ⟨effect⟩

def countdown : Nat → Nat ⊕ Nat
  | 0 => .inl 0
  | n + 1 => .inr n

instance : InstructionModel Instr Code Effect M where
  denote
    | .readLeft => fun _ r => r.1
    | .readRight => fun _ r => r.2
    | .countdown => fun n => pure (countdown n)
  denotePure
    | .readLeft => fun h => nomatch h
    | .readRight => fun h => nomatch h
    | .countdown => fun _ => countdown
  denote_pure
    | .readLeft => fun h => nomatch h
    | .readRight => fun h => nomatch h
    | .countdown => fun _ _ => rfl

def pairing : Elgot.ParallelPairing M := Elgot.Part.parallelPairing.reader

noncomputable def denote {Γ : Ctx Empty Code} {n : Nat} {β : BoundCtx Code n}
    {t : Tm Empty Instr n} {A : Code} (d : Derivation Instr Γ β t A)
    (γ : CtxDen Γ) (values : BoundDen β) : M (Value A) :=
  LetParIter.denote (ε := Effect) pairing d γ values

/-- Read the two independent slots in parallel, retaining their order. -/
def readPair : Derivation Instr Closed .nil
    (tier := .iter) (.par (.op .readLeft .unit) (.op .readRight .unit)) (product number number) :=
  .par (.op .unit) (.op .unit)

def countSeed : Derivation Instr Closed .nil
    (tier := .iter) (.op .readLeft .unit) number :=
  .op .unit

def countStep : Derivation Instr Closed (.snoc .nil number)
    (.case hasCase (.op .countdown (.bv 0))
      (.inl hasCase (.op .readRight .unit)) (.inr hasCase (.bv 0))) (coprod number number) :=
  .case (.op .bv) (.inl (.op .unit)) (.inr .bv)

/-- Use the left slot as a loop counter and read the right slot in the return arm. -/
def countAndRead : Derivation Instr Closed .nil
    (.iter rfl (.op .readLeft .unit)
      (.case hasCase (.op .countdown (.bv 0))
        (.inl hasCase (.op .readRight .unit)) (.inr hasCase (.bv 0)))) number :=
  .iter countSeed countStep

end ReadOnly

namespace Choice

open Elgot

inductive Instr where
  | choose (left right : Nat)
  | step

instance : HasTy Instr Code where
  src
    | .choose _ _ => unit
    | .step => number
  trg
    | .choose _ _ => number
    | .step => coprod number number

instance : HasEff Instr Bool := ⟨fun _ => true⟩

/-- At zero the loop may return 10 or stay at zero. A positive state may
return 20 or take a back edge to zero. -/
def step (n : Nat) : SetM (Nat ⊕ Nat) :=
  ({Sum.inl (if n = 0 then 10 else 20), Sum.inr 0} : Set (Nat ⊕ Nat))

instance : InstructionModel Instr Code Bool SetM where
  denote
    | .choose a b => fun _ => ({a, b} : Set Nat)
    | .step => step
  denotePure _ h := nomatch h
  denote_pure _ h := nomatch h

def denote {Γ : Ctx Empty Code} {n : Nat} {β : BoundCtx Code n}
    {t : Tm Empty Instr n} {A : Code} (d : Derivation Instr Γ β t A)
    (γ : CtxDen Γ) (values : BoundDen β) : SetM (Value A) :=
  LetParIter.denote (ε := Bool) Nondet.parallelPairing d γ values

/-- Combine two independent binary choices. -/
def choosePair (a b c d : Nat) : Derivation Instr Closed .nil
    (tier := .iter) (.par (.op (.choose a b) .unit) (.op (.choose c d) .unit)) (product number number) :=
  .par (.op .unit) (.op .unit)

def chooseSeed : Derivation Instr Closed .nil
    (tier := .iter) (.op (.choose 1 2) .unit) number :=
  .op .unit

def chooseStep : Derivation Instr Closed (.snoc .nil number)
    (.case hasCase (.op .step (.bv 0)) (.inl hasCase (.bv 0)) (.inr hasCase (.bv 0)))
    (coprod number number) :=
  .case (.op .bv) (.inl .bv) (.inr .bv)

/-- Choose a seed, then dispatch the effectful step's return and feedback cases. -/
def chooseLoop : Derivation Instr Closed .nil
    (.iter rfl (.op (.choose 1 2) .unit)
      (.case hasCase (.op .step (.bv 0)) (.inl hasCase (.bv 0)) (.inr hasCase (.bv 0)))) number :=
  .iter chooseSeed chooseStep

end Choice

end Silmaril.Isotope.LetParIter.Models
