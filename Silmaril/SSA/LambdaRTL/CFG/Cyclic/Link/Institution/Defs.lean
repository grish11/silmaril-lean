module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Thms
import Silmaril.SSA.LambdaRTL.CFG.Thms
import Silmaril.SSA.LambdaRTL.Thms

/-! Primitive renaming and the named refinement interpretation of packet CFGs.
A public port keeps its tag. Widening private labels to naturals lets tables
of different sizes be compared in the same named equation. -/

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link

open Comparison

variable {V F F' α : Type} [DecidableEq V] {a b : Nat}

/-- Rename primitive calls, preserving the table layout and packet scopes. -/
def Graph.mapOp (h : F → F') (graph : Graph V F a b) : Graph V F' a b where
  locals := graph.locals
  entry := graph.entry
  block index := (graph.block index).mapOp h
  closed index := by
    simpa only [Block.mapOp, Body.toRegion_mapOp, Region.fv_mapOp] using graph.closed index

/-- A common label type for named graphs with the same public interface. -/
abbrev NamedLabel (outputs : Nat) := Nat ⊕ Fin outputs

/-- A public exit is compared at the same port, independently of private table size. -/
def publicResult (output : Fin b × α) : NamedLabel b × α :=
  (.inr output.1, output.2)

variable [Inhabited V]

/-- The packet CFG as an ordinary mutable CFG at a selected input port.
The named store supplies the packet in the designated register. -/
def Graph.namedRTL (graph : Graph V F a b) (port : Fin a) : CFG V (NamedLabel b) F :=
  (graph.toCFG port).relabel (Sum.map Fin.val id)

/-- Version the named packet CFG into an admitted lexical graph. -/
def Graph.namedSSA (graph : Graph V F a b) (port : Fin a) : LexicalGraph V (NamedLabel b) F :=
  Comparison.version (graph.namedRTL port)

/-- Refinement in one model quantifies over all input ports and packets. -/
def Sat (model : PairModel F Part α) (lhs rhs : Arrow V F α a b) : Prop :=
  ∀ input, observe model lhs input ≤ observe model rhs input

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link
