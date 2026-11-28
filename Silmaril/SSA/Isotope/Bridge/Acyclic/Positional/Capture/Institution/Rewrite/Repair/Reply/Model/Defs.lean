module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Kleisli.Defs
public import Silmaril.Semantics.NondeterministicTrace.Thms
public import Mathlib.Algebra.FreeMonoid.Basic

/-! # A small tagged trace model with both replies at every request -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply

open Kleisli (value)
open Silmaril.Semantics.NondeterministicTrace (Tagged)
open LambdaSSA.Region (packedExitType)
open LetIter.Semantics.Categorical (boundEnv)

inductive Event where
  | emit (bit : Bool)
  | answer (request right : Bool)

abbrev Log := FreeMonoid Event
abbrev Trace := Tagged Log Bool
abbrev Outcome (A : Type) := Except Bool A × Log

def prepend {A : Type} (event : Event) (outcome : Outcome A) : Outcome A :=
  (outcome.1, FreeMonoid.of event * outcome.2)

/-- Read one observed reply and remove its event from the selected traces. -/
def afterReply {A : Type} (request right : Bool) (s : Set (Outcome A)) : Set (Outcome A) :=
  prepend (.answer request right) ⁻¹' s

/-- The independently specified finite paths of a normal tree. -/
def Normal.outcomesWith {R A : Type} (success : R → A) : Normal R → Set (Outcome A)
  | .ret r => {(.ok (success r), 1)}
  | .stop fault => {(.error fault, 1)}
  | .emit bit next => prepend (.emit bit) '' next.outcomesWith success
  | .ask request l r =>
    (prepend (.answer request false) '' l.outcomesWith success) ∪
      (prepend (.answer request true) '' r.outcomesWith success)

def Normal.outcomes {A : Type} (success : A) (p : Normal) : Set (Outcome A) :=
  p.outcomesWith (fun _ => success)

def model : Isotope.Semantics.InstructionModel value signature.Instr Trace where
  eval
    | .emit bit => fun _ => Tagged.ofOutcomes {(.ok PUnit.unit, FreeMonoid.of (.emit bit))}
    | .ask req => fun _ => Tagged.ofOutcomes {
      (.ok (.inl PUnit.unit), FreeMonoid.of (.answer req false)),
      (.ok (.inr PUnit.unit), FreeMonoid.of (.answer req true))}
    | .stop fault => fun _ => Tagged.incomplete fault 1

/-- Run the actual packed term emitted by the captured grammar. -/
noncomputable def Tree.programOutcomes (p : Tree) (tail : List Sorts) :
    Set (Outcome (value (packedExitType (Ty.unit :: tail)))) :=
  (Kleisli.run model (Rewrite.returnUnit tail (p.operand .nil)).toLetCase.2
    (boundEnv value (β := .nil) PUnit.unit)).outcomes

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply
