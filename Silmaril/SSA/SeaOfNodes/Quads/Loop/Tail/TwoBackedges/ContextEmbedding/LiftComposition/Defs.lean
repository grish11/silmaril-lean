module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Composition.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Factorization.Ports.Defs

/-! Lift a valuation through two typed capture maps and independently check both compiler routes. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.LiftComposition

open SeaOfNodes.Diamond (dataPorts)
open Silmaril.MLIR.Arith (Width)
open RVSDG (Port)
open Composition (thenMap)
open Factorization (extendInput liftChecked)
open Identification (PortMap Refusal reduct)
open Reindex.Guarded.Institution (AdmittedAt Generated Valuation)
open Reindex.Guarded.Institution renaming Signature → EntrySignature

variable {S T U : EntrySignature} {result : Width}

/-- The requested fill constrains precisely the slots with no old preimage. -/
def AgreesOnUnused (map : PortMap S T) (target fill : Valuation T) : Prop :=
  ∀ t (port : Port (dataPorts T.regs) t),
    (¬ ∃ old, map t old = port) → target.get port = fill.get port

/-- Propagate the final candidate back through the second map. A slot unused
by the first map can share a final slot with a used intermediate slot. -/
def intermediateFill (first : PortMap S T) (second : PortMap T U)
    (input : Valuation S) (fill : Valuation U) : Valuation T :=
  reduct second (extendInput (thenMap first second) input fill)

/-- Run the two existing valuation checks with a consistent intermediate fill. -/
def liftStaged (first : PortMap S T) (second : PortMap T U)
    (input : Valuation S) (fill : Valuation U) : Option (Valuation T × Valuation U) := do
  let mid ← liftChecked first input (intermediateFill first second input fill)
  let target ← liftChecked second mid fill
  pure (mid, target)

/-- Sentence operands retain the three independently successful compiler calls. -/
structure Compared (first : PortMap S T) (second : PortMap T U) (result : Width) where
  source : AdmittedAt S result
  intermediate : Generated T result
  staged : Generated U result
  direct : Generated U result
  firstOk : Identification.compile first source = .ok intermediate
  secondOk : Identification.compile second intermediate.source = .ok staged
  directOk : Identification.compile (thenMap first second) source = .ok direct

inductive Refused where
  | first (reason : Refusal)
  | second (reason : Refusal)
  | direct (reason : Refusal)
  deriving DecidableEq, Repr

/-- Run the actual guarded compiler at the intermediate and final signatures
and independently at the composed map. -/
def compare (first : PortMap S T) (second : PortMap T U) (p : AdmittedAt S result) :
    Except Refused (Compared first second result) :=
  match firstOk : Identification.compile first p with
  | .error reason => .error (.first reason)
  | .ok intermediate =>
    match secondOk : Identification.compile second intermediate.source with
    | .error reason => .error (.second reason)
    | .ok staged =>
      match directOk : Identification.compile (thenMap first second) p with
      | .error reason => .error (.direct reason)
      | .ok direct => .ok ⟨p, intermediate, staged, direct, firstOk, secondOk, directOk⟩

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.LiftComposition
