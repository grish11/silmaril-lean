module

public import Silmaril.Logic.BrookesSC.Concrete.Defs
public import Silmaril.Semantics.Brookes.Iteration.Thms
public import Silmaril.Semantics.Brookes.Parallel.Pairing.Defs
public import Silmaril.SSA.Isotope.LetParIter.Interpretation.Defs

/-! # A concrete SC instruction model for LetParIter -/

@[expose] public section

namespace Silmaril.Isotope.BrookesLetParIter

open Silmaril.Elgot
open Silmaril.Logic.BrookesSC
open Silmaril.Semantics.Brookes
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics

/-- Two threads use one word cell and one mutex. -/
def world : World where
  Thread := Bool
  Cell := Unit
  Value _ := Nat
  Mutex := Unit
  ExternalSort := Empty
  ExternalReply x := x.elim

instance : DecidableEq world.Thread := inferInstanceAs (DecidableEq Bool)
instance : DecidableEq world.Cell := inferInstanceAs (DecidableEq Unit)
instance : DecidableEq world.Mutex := inferInstanceAs (DecidableEq Unit)

abbrev Store := Concrete.Store world
abbrev M : Type → Type := Behavior Store
abbrev SCType := Ty Unit
abbrev word : SCType := .base ()

/-- The word sort and its freely generated compound types. -/
def value : SCType → Type
  | .base _ => Nat
  | .product a b => value a × value b
  | .unit => Unit
  | .coprod a b => Sum (value a) (value b)
  | .empty => Empty

def coerce : {A B : SCType} → Ty.Subty A B → value A → value B
  | _, _, .refl _, a => a
  | _, _, .trans f g, a => coerce g (coerce f a)
  | _, _, .product f g, (a, b) => (coerce f a, coerce g b)
  | _, _, .coprod f g, a => Sum.map (coerce f) (coerce g) a
  | _, _, .empty _, a => a.elim
  | _, _, .unit _, _ => ()

instance : TypeModel SCType where
  interp := value
  productEquiv _ _ := Equiv.refl _
  unitEquiv := Equiv.refl _
  coprodEquiv _ _ := Equiv.refl _
  emptyEquiv := Equiv.refl _
  coe := coerce

instance : LawfulTypeModel SCType where
  coe_refl _ := rfl
  coe_trans _ _ := rfl
  coe_product _ _ p := by cases p; rfl
  coe_coprod _ _ _ := rfl
  coe_empty _ a := a.elim
  coe_unit _ _ := rfl

/-- Primitive instructions use the landed fixed-world SC implementation.
Identity is a value operation, and is the only instruction marked pure. -/
inductive Instr where
  | identity
  | load (thread : Bool)
  | store (thread : Bool)
  | acquire (thread : Bool)
  | release (thread : Bool)

instance : HasTy Instr SCType where
  src
    | .identity | .store _ => word
    | _ => .unit
  trg
    | .identity | .load _ => word
    | _ => .unit

instance : HasEff Instr Bool where
  eff
    | .identity => false
    | _ => true

def eval : (op : Instr) → value (instrSrc op) → M (value (instrTrg op))
  | .identity, a => Behavior.ret a
  | .load thread, _ => Concrete.primitive (.load thread .scAtomic ())
  | .store thread, a => Concrete.primitive (.store thread .scAtomic () a)
  | .acquire thread, _ => Concrete.primitive (.acquire thread ())
  | .release thread, _ => Concrete.primitive (.release thread ())

/-- The witness carried by a bottom-effect proof is the ordinary identity. -/
def evalPure (op : Instr) (h : (instrEff op : Bool) = ⊥) :
    value (instrSrc op) → value (instrTrg op) := by
  cases op
  · exact id
  all_goals cases h

instance : InstructionModel Instr SCType Bool M where
  denote := eval
  denotePure := evalPure
  denote_pure op h a := by
    cases op
    · rfl
    all_goals cases h

/-- The general closed-shuffle pairing specialized to this SC world. -/
abbrev pairing : ParallelPairing M := Behavior.parallelPairing Store

/-- A store with the given cell value and mutex owner. -/
def state (wordValue : Nat) (owner : Option Bool) : Store :=
  ⟨fun _ => wordValue, fun _ => owner⟩

end Silmaril.Isotope.BrookesLetParIter
