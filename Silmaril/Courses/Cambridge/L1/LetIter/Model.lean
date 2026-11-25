module

public import Silmaril.Courses.Cambridge.L1.EffectfulDenotational.Defs
public import Silmaril.Courses.Cambridge.L1.Typing
public import Silmaril.SSA.Isotope.LetIter.Thms

/-! The LetIter instruction model for L1 uses the same state, error and
partiality monad as its denotation. Booleans are sums of units, so conditional
control can use LetIter's own case construct. -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L1.LetIter

open Silmaril.Isotope.LetIter.ProofRelevant.Semantics
open EffectfulDenotational (Computation)

abbrev TargetTy := Silmaril.Ty Unit
abbrev intTy : TargetTy := .base ()
abbrev unitTy : TargetTy := .unit
abbrev boolTy : TargetTy := .coprod unitTy unitTy

def lowerTy : L1.Ty → TargetTy
  | .int => intTy
  | .bool => boolTy
  | .unit => unitTy

def interp : TargetTy → Type
  | .base _ => Int
  | .product a b => interp a × interp b
  | .coprod a b => interp a ⊕ interp b
  | .unit => Unit
  | .empty => Empty

def coerce {A B : TargetTy} : Silmaril.Isotope.Ty.Subty A B → interp A → interp B
  | .refl _ => id
  | .trans f g => coerce g ∘ coerce f
  | .product f g => Prod.map (coerce f) (coerce g)
  | .coprod f g => Sum.map (coerce f) (coerce g)
  | .empty _ => Empty.elim
  | .unit _ => fun _ => ()

instance : TypeModel TargetTy where
  interp := interp
  productEquiv A B := Equiv.refl (interp A × interp B)
  unitEquiv := Equiv.refl Unit
  coprodEquiv A B := Equiv.refl (interp A ⊕ interp B)
  emptyEquiv := Equiv.refl Empty
  coe := coerce

def boolTag (b : Bool) : Unit ⊕ Unit := if b then .inl () else .inr ()

def compare (l r : Int) : Unit ⊕ Unit := boolTag (l ≥ r)

/-- Re-express a typed result as the value syntax used by L1 configurations. -/
def value : (T : L1.Ty) → TyDen (lowerTy T) → Expr
  | .int, n => .int n
  | .bool, .inl _ => .bool true
  | .bool, .inr _ => .bool false
  | .unit, _ => .skip

inductive Instr where
  | literal (n : Int)
  | read (loc : Loc)
  | write (loc : Loc)
  | add
  | ge

instance : HasTy Instr TargetTy where
  src
    | .literal _ | .read _ => unitTy
    | .write _ => intTy
    | .add | .ge => .product intTy intTy
  trg
    | .literal _ | .read _ | .add => intTy
    | .write _ => unitTy
    | .ge => boolTy

/-- The instruction effect flag marks store access. -/
instance : HasEff Instr Bool where
  eff
    | .read _ | .write _ => true
    | _ => false

def instrDenote : (i : Instr) → TyDen (instrSrc (τ := TargetTy) i) →
    Computation (TyDen (instrTrg (τ := TargetTy) i))
  | .literal n, _ => pure n
  | .read loc, _ => EffectfulDenotational.read loc >>= fun v =>
      match v with
      | .int n => pure n
      | _ => throw ()
  | .write loc, n => EffectfulDenotational.write loc n >>= fun _ => pure ()
  | .add, (l, r) => pure (Int.add l r)
  | .ge, (l, r) => pure (compare l r)

def instrPure : (i : Instr) → (instrEff i : Bool) = (⊥ : Bool) →
    TyDen (instrSrc (τ := TargetTy) i) → TyDen (instrTrg (τ := TargetTy) i)
  | .literal n, _, _ => n
  | .read _, h, _ => nomatch h
  | .write _, h, _ => nomatch h
  | .add, _, (l, r) => Int.add l r
  | .ge, _, (l, r) => compare l r

instance : InstructionModel Instr TargetTy Bool Computation where
  denote := instrDenote
  denotePure := instrPure
  denote_pure := by
    intro i h a
    cases i with
    | read | write => cases h
    | literal | add | ge => rfl

end Silmaril.Courses.Cambridge.L1.LetIter
