module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.Institution.Defs

/-! Native loop equations and finite observations of the emitted guarded rows. -/

@[expose] public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL.SSA (Prog)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (Reg WordOp model word)
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA (Primitive inputEnv instruction)
open Silmaril.SSA.SeaOfNodes.Loop.Institution (Equation Program)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic (packResult)
open Silmaril.Isotope.LambdaSSA (Region)
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)

abbrev wordSignature : Silmaril.SSA.SeaOfNodes.Diamond.Institution.Signature.{0, 0} Unit :=
  ⟨WordOp⟩

variable {arity : Nat}

/-- Package the same native graph, retaining its two incoming columns. -/
def Plan.program (p : Plan arity) : Program wordSignature (wordSorts arity) word :=
  ⟨wordSorts arity, [], p.sigs, p.graph⟩

def Plan.equation (left right : Plan arity) : Equation wordSignature :=
  ⟨wordSorts arity, word, left.program, right.program⟩

/-- The relational view of a partial observation, with all final memory. -/
abbrev Observation := Set (Word × Memory)

def rtlObservation (target : Prog Reg) (input : WordTuple arity) (initial : Memory) : Observation :=
  { result | target.oracle 0 (words input) initial [result.1] result.2 }

def lambdaObservation (target : Region (Primitive WordOp)) (input : WordTuple arity)
    (initial : Memory) : Observation :=
  { result | Eval (instruction model) (inputEnv model input) target
      initial 0 (packResult model (out := word) result.1) result.2 }

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows
