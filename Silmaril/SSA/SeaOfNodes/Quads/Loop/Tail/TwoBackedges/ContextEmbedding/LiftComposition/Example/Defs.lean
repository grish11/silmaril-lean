module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.LiftComposition.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Factorization.Example.Defs

/-! Two contractions with a shared intermediate slot and an unused final i16. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.LiftComposition.Example

open SeaOfNodes.Loop.MLIR.CF (model evalOp)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Identification (PortMap reduct)
open Identification.Example (old rhs original changesAdmission)
open Factorization (liftChecked)
open Factorization.Example (captureMap finalSignature oldInput fill gap)
open SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example (width)
open Reindex.Guarded.Institution (Generated Valuation)
open Reindex.Guarded.Institution renaming Signature → EntrySignature
open Weakening.Guarded.Example (captureWidth)

/-- Identify the two old addends but leave the second addend's intermediate
slot available. The second map then sends both intermediate slots to one final port. -/
def first : PortMap old old := fun _ => fun
  | .tail (.tail (.tail .head)) => .tail (.tail .head)
  | port => port

def second : PortMap old finalSignature := captureMap

/-- Display the value reconstructed for the unused intermediate addend
and the unchanged final gap. -/
def liftValues (right : Word width) (wide : Word captureWidth) : Option (Nat × Nat) :=
  (liftStaged first second (oldInput right true) (fill wide)).map fun (mid, target) =>
    ((mid.get rhs).toNat, (target.get gap).toNat)

/-- A plain reduct of the final fill uses zero at the shared slot. After
the first lift, the two intermediate addends would therefore disagree. -/
def naiveSucceeds : Bool :=
  ((liftChecked first (oldInput 7 true) (reduct second (fill 0))).bind fun mid =>
    liftChecked second mid (fill 0)).isSome

def compared : Option (Compared first second width) := do
  let p ← original.toOption
  (compare first second p).toOption

def compilerRefusal : Option Refused := do
  let p ← changesAdmission.toOption
  match compare first second p with
  | .error reason => some reason
  | .ok _ => none

/-- Real intermediate, staged-final and direct-final returns, with each
backend using its own budget. -/
def run (wide : Word captureWidth) (side : Bool) :
    Option ((Option Nat × Option Nat) × (Option Nat × Option Nat) × (Option Nat × Option Nat)) := do
  let pair ← compared
  let (mid, target) ← liftStaged first second (oldInput 7 side) (fill wide)
  let runAt {S : EntrySignature} (p : Generated S width) (input : Valuation S) :=
    ((p.artifacts.cf.run evalOp (if side then 6 else 7) (encodeValues input)).map
      (fun env => (env.get .here).toNat),
     (p.artifacts.numbered.2.run (Join.model model) 1 input).map
      (fun packet => (packet.get .head).toNat))
  return (runAt pair.intermediate mid, runAt pair.staged target, runAt pair.direct target)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.LiftComposition.Example
