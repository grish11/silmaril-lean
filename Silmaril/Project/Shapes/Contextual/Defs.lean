module

public import Silmaril.Project.Shapes.C.Defs

/-! State-sensitive contextual obligations. Unlike a scalar-only `Meaning`, the
observation retains caller-visible memory and environment state. Contexts are
input data, never certificates of translation correctness. Core calls execute
actual bodies in the pinned program; a supplied contract does not replace them.
The machine totality clause promises a first-return run and checks every
first-return outcome; it does not assert all-path termination of a nondeterministic
machine. Safety of every admitted Core entry and joint entry existence are
separate obligations, preventing an empty/undefined source context from counting.
-/
@[expose] public section
namespace Silmaril.Project.Shapes.Contextual
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.X86 (MState FnContract)
open Silmaril.Project.Shapes

/-- A callee contract is a local semantic requirement, not an assumed C-to-machine
refinement. Source bodies remain in `F.file`; contracts must be discharged for
those actual bodies. The caller's desired result is absent from this structure. -/
structure Callee where
  source : Silmaril.Compiler.CompilesTo.Source State Val
  sourceEntry : State → Prop
  sourcePost : State → State → Val → Prop
  machine : FnContract.Spec MState

/-- Explicit call assumptions, independently about each execution model. -/
def Callee.Holds (c : Callee) (M : Model) : Prop :=
  (∃ s, c.sourceEntry s) ∧ Nonvacuous M c.machine ∧
  (∀ s, c.sourceEntry s → c.source.Safe s ∧
    ∀ t v, Relation.ReflTransGen c.source.step s t → c.source.final t v →
      c.sourcePost s t v) ∧ c.machine.Strict M

/-- The instance supplies concrete source/ABI entries, initial memory relation,
write footprint and observations. No validity/refinement law is accepted here.
`Input` must describe the admitted data, not contain a proof of the goal. -/
structure Context (Input Observation : Type) where
  sourceEntry : Input → State → Prop
  machineEntry : Input → MState → Prop
  related : Input → State → MState → Prop
  footprint : Input → MState → Nat → Prop
  sourceObservation : Input → State → State → Val → Observation
  machineObservation : Input → MState → MState → Observation
  callees : List Callee := []

variable {Input Observation : Type}

def Context.Initial (C : Context Input Observation) (M : Model)
    (i : Input) (s : State) (m : MState) : Prop :=
  C.sourceEntry i s ∧ C.machineEntry i m ∧ C.related i s m ∧
  M.live m ∧ FnContract.AbiEntry (M.core m) (M.mem m)

/-- A real source procedure, actual machine placement and full-state context.
All input instances must admit a joint entry. Source safety is an obligation,
not a premise permitting every supported input to disappear through UB. Local callee contracts are additional obligations, never an implication
premise that could make the caller result vacuous. -/
def Obligation {sig : Silmaril.X86.SystemV.CApi.Signature}
    (F : C.CFn sig) (M : Model) (p : Placement)
    (C : Context Input Observation) : Prop :=
  (∀ i, ∃ s m, C.Initial M i s m) ∧
  (∀ i s m, C.Initial M i s m → p.Entered m ∧ (F.source []).Safe s) ∧
  (∀ c ∈ C.callees, c.Holds M) ∧
    ∀ i s m, C.Initial M i s m →
      (∃ t, FnContract.FirstReturn M m t) ∧
      ∀ t, FnContract.FirstReturn M m t →
        FnContract.AbiReturn (M.core m) (M.mem m) (M.core t) ∧
        (M.mem m).WritesWithin (M.mem t) (C.footprint i m) ∧
        (∃ u v, Relation.ReflTransGen (F.source []).step s u ∧
          (F.source []).final u v ∧
          C.sourceObservation i s u v = C.machineObservation i m t)

end Silmaril.Project.Shapes.Contextual
