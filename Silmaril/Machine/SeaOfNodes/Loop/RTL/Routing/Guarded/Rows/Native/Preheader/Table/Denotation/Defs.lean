module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Defs
public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Institution.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.Denotation

/-! Partial observations of the native graph and its actual target programs. -/

@[expose] public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL.SSA (Prog)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg WordOp model)
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA (Primitive)
open Silmaril.Isotope.LambdaSSA (Region)

variable {arity : Nat} {entrySigs sigs : List (List PortTy)}

/-- Attach the initial memory to the native partial result of this pure loop. -/
noncomputable def nativeDenote (g : SourceWithEntry arity entrySigs sigs)
    (input : WordTuple arity) (initial : Memory) : Part (Word × Memory) :=
  (g.denote model input).map (fun word => (word, initial))

/-- Select the word and final memory witnessed by the actual RTL call oracle. -/
noncomputable def rtlDenote (target : Prog Reg) (input : WordTuple arity)
    (initial : Memory) : Part (Word × Memory) :=
  ⟨∃ result, result ∈ Rows.rtlObservation target input initial, Classical.choose⟩

/-- Select the word and final memory witnessed by actual CFG evaluation at
exit zero with the packed singleton payload. -/
noncomputable def lambdaDenote (target : Region (Primitive WordOp)) (input : WordTuple arity)
    (initial : Memory) : Part (Word × Memory) :=
  ⟨∃ result, result ∈ Rows.lambdaObservation target input initial, Classical.choose⟩

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table
