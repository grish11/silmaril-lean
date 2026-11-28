module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Identification.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Thms

/-! Enumerate the image of a typed port map and reconstruct candidate valuations. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Factorization

open SeaOfNodes.Diamond (Val ValueSort dataPorts)
open SeaOfNodes.Loop.SCCP (decideTupleCovers)
open SeaOfNodes.MLIR (Word)
open Silmaril.MLIR.Arith (Width)
open RVSDG (Port)
open Identification (BankMap PortMap ports reduct)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (EntryFacts)
open Reindex.Guarded.Institution (Valuation)
open Reindex.Guarded.Institution renaming Signature → EntrySignature

variable {old new : List (ValueSort Width)} {t : SeaOfNodes.Diamond.Ty Width}
variable {S T : EntrySignature}

def preimageCandidate (map : BankMap old new) (target : Port (dataPorts new) t)
    (candidate : Sigma (Port (dataPorts old))) : Option (Port (dataPorts old) t) :=
  if same : slot (map candidate.1 candidate.2) = slot target then
    let sort : candidate.1 = t := congrArg Sigma.fst (Reindex.slot_eq (map candidate.1 candidate.2) target same)
    some (sort ▸ candidate.2)
  else none

/-- The first typed old port mapped to the given target slot, if one exists. -/
def preimage (map : BankMap old new) (target : Port (dataPorts new) t) :
    Option (Port (dataPorts old) t) :=
  (ports (dataPorts old)).findSome? (preimageCandidate map target)

/-- Coordinates in one fibre must carry the same input value. -/
def Consistent (map : PortMap S T) (input : Valuation S) : Prop :=
  ∀ t (left right : Port (dataPorts S.regs) t),
    map t left = map t right → input.get left = input.get right

/-- Read the first representative of each used slot. Unused slots take
their values from the supplied target valuation. -/
def extendInput (map : PortMap S T) (input : Valuation S) (fill : Valuation T) : Valuation T :=
  tabulate (F := Val Word) (dataPorts T.regs) fun target =>
    match preimage map target with
    | some source => input.get source
    | none => fill.get target

/-- Check that the candidate reduces to the requested old valuation.
The existing tuple coverage decision checks exact singleton facts. -/
def liftChecked (map : PortMap S T) (input : Valuation S) (fill : Valuation T) :
    Option (Valuation T) :=
  let candidate := extendInput map input fill
  let exactFacts : EntryFacts S.regs := tabulate (dataPorts S.regs) fun p => .constant (input.get p)
  if @decide _ (@decideTupleCovers _ _ _ S.bankEq exactFacts (reduct map candidate)) then
    some candidate
  else none

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Factorization
