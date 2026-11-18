module

public import Silmaril.Semantics.Region.Semantic.Defs
public import Mathlib.Order.CompleteLattice.Basic

/-! # Abstract may-effect upper envelopes

Observation and coverage belong to an interpretation, outside the positive
region-law lattice. The complete lattice can be a powerset, product, or a
coarser domain with Top; no finite enumeration or basic-block partition is
required. Bounds below describe possible effects, never mandatory effects.
-/

@[expose] public section
namespace Silmaril.Semantics.Region.Effects
universe u v w x y
variable {S : Type u} {L : Type v} {Ev : Type w} {Stop : Type x} {E : Type y}

/-- Least sound upper bound of every observable effect of every admitted
internal prefix or boundary-crossing step. Diverging prefixes are included. -/
noncomputable def envelope [CompleteLattice E] (T : TransitionSystem S L Ev Stop)
    (A : S → Prop) (U : L → Prop) (observe : Ev → E) : E :=
  ⨆ e, ⨆ (_ : MayEffect T A U e), observe e

def SoundBound [LE E] (T : TransitionSystem S L Ev Stop) (A : S → Prop)
    (U : L → Prop) (observe : Ev → E) (bound : E) : Prop :=
  ∀ e, MayEffect T A U e → observe e ≤ bound

/-- Must effects quantify over an explicitly chosen outcome/trace family.
The separate witness prevents vacuity when the chosen family is empty;
termination/divergence policy is the client's choice of `runs`. -/
def MustOccur (runs : List Ev → Prop) (e : Ev) : Prop :=
  (∃ es, runs es) ∧ ∀ es, runs es → e ∈ es

/-- Sample powerset observation vocabulary. Clients may use each component
separately or a product of abstract domains; these are not ISA semantics. -/
inductive Atom (Reg Addr Instr Func Syscall : Type*) where
  | clobber (r : Reg)
  | read (a : Addr)
  | write (a : Addr)
  | instruction (i : Instr)
  | call (f : Func)
  | syscall (n : Syscall)
  | use (r : Reg)
  | define (r : Reg)
  | ub | trap | raise

def clobbers {R A I F N} (effects : Set (Atom R A I F N)) : Set R := {r | .clobber r ∈ effects}
def instructions {R A I F N} (effects : Set (Atom R A I F N)) : Set I := {i | .instruction i ∈ effects}
def calls {R A I F N} (effects : Set (Atom R A I F N)) : Set F := {f | .call f ∈ effects}
def syscalls {R A I F N} (effects : Set (Atom R A I F N)) : Set N := {n | .syscall n ∈ effects}
def uses {R A I F N} (effects : Set (Atom R A I F N)) : Set R := {r | .use r ∈ effects}
def definitions {R A I F N} (effects : Set (Atom R A I F N)) : Set R := {r | .define r ∈ effects}

def reads {R A I F N} (effects : Set (Atom R A I F N)) : Set A := {a | .read a ∈ effects}
def writes {R A I F N} (effects : Set (Atom R A I F N)) : Set A := {a | .write a ∈ effects}
def touches {R A I F N} (effects : Set (Atom R A I F N)) : Set A := reads effects ∪ writes effects

/-- Upward-exposed uses need definite definitions to kill later uses. A
may-clobber/write set is not a valid substitute for `definiteDefs`. -/
structure UseDef (R : Type u) where
  uses : Set R
  definiteDefs : Set R

def UseDef.sequence {R : Type u} (a b : UseDef R) : UseDef R :=
  ⟨a.uses ∪ (b.uses \ a.definiteDefs), a.definiteDefs ∪ b.definiteDefs⟩
def UseDef.selection {R : Type u} (a b : UseDef R) : UseDef R :=
  ⟨a.uses ∪ b.uses, a.definiteDefs ∩ b.definiteDefs⟩

end Silmaril.Semantics.Region.Effects
