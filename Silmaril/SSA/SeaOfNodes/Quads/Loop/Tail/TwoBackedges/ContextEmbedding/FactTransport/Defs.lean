module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Identification.Defs

/-! Compatibility for intersecting a typed source fact block. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FactTransport

open SeaOfNodes.Diamond (Val ValueSort dataPorts)
open SeaOfNodes.MLIR (Word)
open Silmaril.MLIR.Arith (Width)
open RVSDG (Port)
open Identification (BankMap)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (EntryFacts)

variable {old new : List (ValueSort Width)}

/-- An empty source coordinate or two different constants in one fibre
make the intersection unsatisfiable. -/
def Compatible (map : BankMap old new) (facts : EntryFacts old) : Prop :=
  (∀ t (p : Port (dataPorts old) t), facts.get p ≠ .bottom) ∧
  ∀ t (left right : Port (dataPorts old) t) (a b : Val Word t),
    map t left = map t right →
    facts.get left = .constant a → facts.get right = .constant b → a = b

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FactTransport
