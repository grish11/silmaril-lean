module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Composition.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Factorization.Ports.Defs

/-! Report a write alias hidden from the composite check by an unused intermediate port. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.WriteAdmission

open SeaOfNodes.Diamond (ValueSort dataPorts)
open SeaOfNodes.Loop.MLIR.CF (Op)
open Silmaril.MLIR.Arith (Width)
open RVSDG (Port)
open Identification (BankMap ports quads)
open Factorization (preimage preimageCandidate)

variable {old middle new : List (ValueSort Width)} {out : ValueSort Width}
variable {t : SeaOfNodes.Diamond.Ty Width}

/-- The occurrence indexes the actual ordered write list. The conflicting
preimage has the writer's sort. -/
structure Conflict (p : Program Op middle out) where
  occurrence : Fin (quads p).length
  other : Port (dataPorts middle) (.value ((quads p).get occurrence).result)

def Conflict.written {p : Program Op middle out} (c : Conflict p) :
    Port (dataPorts middle) (.value ((quads p).get c.occurrence).result) :=
  ((quads p).get c.occurrence).dest

def OutsideAlias (first : BankMap old middle) (second : BankMap middle new)
    (written other : Port (dataPorts middle) t) : Prop :=
  slot other ≠ slot written ∧
    second t other = second t written ∧
    ¬ ∃ source, first t source = other

def Conflict.Valid {p : Program Op middle out} (c : Conflict p)
    (first : BankMap old middle) (second : BankMap middle new) : Prop :=
  OutsideAlias first second c.written c.other

/-- Find a distinct preimage of the written target that the first map
never reaches. -/
def findOutsideAlias (first : BankMap old middle) (second : BankMap middle new)
    (written : Port (dataPorts middle) t) : Option (Port (dataPorts middle) t) :=
  (ports (dataPorts middle)).findSome? fun candidate =>
    (preimageCandidate second (second t written) candidate).filter fun other =>
      (slot other != slot written) && (preimage first other).isNone

/-- Scan write occurrences in the order used by the existing structural check. -/
def diagnose (first : BankMap old middle) (second : BankMap middle new)
    (p : Program Op middle out) : Option (Conflict p) :=
  (List.finRange (quads p).length).findSome? fun occurrence =>
    (findOutsideAlias first second ((quads p).get occurrence).dest).map (Conflict.mk occurrence)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.WriteAdmission
