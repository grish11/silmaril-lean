module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Defs

/-! Identify typed entry ports with a checked restriction on mutable writes. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Identification

open SeaOfNodes.Diamond (Ty Val ValueSort dataPorts)
open SeaOfNodes.Diamond.SCCP (Fact)
open SeaOfNodes.Loop.MLIR.CF (Op)
open SeaOfNodes.MLIR (Word)
open Silmaril.MLIR.Arith (Width)
open RVSDG (Port Tuple)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (Admitted EntryFacts admit)
open Reindex.Guarded.Institution (AdmittedAt Generated Valuation)
open Reindex.Guarded.Institution renaming Signature → EntrySignature

abbrev BankMap (old new : List (ValueSort Width)) :=
  ∀ t, Port (dataPorts old) t → Port (dataPorts new) t

abbrev PortMap (S T : EntrySignature) := BankMap S.regs T.regs

variable {S T : EntrySignature} {old new : List (ValueSort Width)} {out : ValueSort Width}
variable {result : Width}

/-- Each old port reads its image. Identified old positions therefore read
the same target value. -/
def pull {F : SeaOfNodes.Diamond.Ty Width → Type} (map : BankMap old new)
    (input : Tuple F (dataPorts new)) : Tuple F (dataPorts old) :=
  tabulate (dataPorts old) fun port => input.get (map _ port)

def reduct (map : PortMap S T) (input : Valuation T) : Valuation S := pull map input

def quad (map : BankMap old new) (q : Quad Op old) : Quad Op new :=
  ⟨q.ins, q.result, map _ q.dest, q.op, q.operands.map map⟩

/-- Transport every typed destination, operand and control/return port. The
write check is separate because the port map can identify registers. -/
def program (map : BankMap old new) (p : Program Op old out) : Program Op new out where
  preheader := p.preheader.map (quad map)
  header := p.header.map (quad map)
  again := map _ p.again
  select := map _ p.select
  result := map _ p.result
  feedback side := (p.feedback side).map (quad map)

universe u

/-- Enumerate typed positions, including separate occurrences at equal sorts. -/
def ports {T : Type u} : (ts : List T) → List (Sigma (Port ts))
  | [] => []
  | t :: ts => ⟨t, .head⟩ :: (ports ts).map (fun p => ⟨p.1, .tail p.2⟩)

def quads (p : Program Op old out) : List (Quad Op old) :=
  p.preheader ++ p.header ++ p.feedback true ++ p.feedback false

/-- A write may only target a singleton fibre of the port map. -/
def SafeWrite (map : BankMap old new) (q : Quad Op old) : Prop :=
  ∀ t (port : Port (dataPorts old) t), slot (map t port) = slot (map _ q.dest) → slot port = slot q.dest

def SafeWrites (map : BankMap old new) (p : Program Op old out) : Prop :=
  ∀ q ∈ quads p, SafeWrite map q

def checkWrites (map : BankMap old new) (p : Program Op old out) : Bool :=
  (quads p).all fun q =>
    (ports (dataPorts old)).all fun port =>
      (slot (map port.1 port.2) != slot (map _ q.dest)) || (slot port.2 == slot q.dest)

/-- Intersect entry constraints. Distinct constants, and any bottom fact,
have empty intersection. Starting at overdefined permits extra target ports. -/
def merge (sort : ValueSort Width) (left right : Fact Word (.value sort)) : Option (Fact Word (.value sort)) :=
  letI : DecidableEq (Val Word (.value sort)) := Weakening.Guarded.captureEq sort
  match left, right with
  | .bottom, _ | _, .bottom => none
  | .overdefined, fact | fact, .overdefined => some fact
  | .constant a, .constant b => if a = b then some (.constant a) else none

def collectFacts : {old : List (ValueSort Width)} → EntryFacts old → BankMap old new →
    EntryFacts new → Option (EntryFacts new)
  | [], .nil, _, accumulated => some accumulated
  | sort :: _, .cons head rest, map, accumulated => do
    let dest := map (.value sort) .head
    let merged ← merge sort head (accumulated.get dest)
    collectFacts rest (fun t port => map t (.tail port)) (write dest merged accumulated)

def pushFacts (map : BankMap old new) (facts : EntryFacts old) : Option (EntryFacts new) :=
  collectFacts facts map (tabulate (dataPorts new) fun _ => .overdefined)

inductive Refusal where
  | aliasedWrite
  | incompatibleFacts
  | checker (reason : SCCP.Dispatch.Refusal)
  deriving DecidableEq, Repr

/-- Check alias safety and guard consistency, then rerun the original FIFO
checker on the transported program and facts. -/
def replay (map : PortMap S T) (p : AdmittedAt S result) : Except Refusal (AdmittedAt T result) :=
  let source := @Admitted.source _ _ S.bankEq p
  if checkWrites map source then
    match pushFacts map (@Admitted.facts _ _ S.bankEq p) with
    | none => .error .incompatibleFacts
    | some facts =>
      match @admit _ _ T.bankEq (program map source) facts with
      | .error reason => .error (.checker reason)
      | .ok checked => .ok checked
  else .error .aliasedWrite

def compile (map : PortMap S T) (p : AdmittedAt S result) : Except Refusal (Generated T result) :=
  (replay map p).map Generated.lower

/-- A source and its successful compilation, usable in equations and termination sentences. -/
structure Compiled (map : PortMap S T) (result : Width) where
  source : AdmittedAt S result
  target : Generated T result
  success : compile map source = .ok target

/-- Retain the checker outcome as the witness for sentence translation. -/
def certify (map : PortMap S T) (p : AdmittedAt S result) : Except Refusal (Compiled map result) :=
  match success : compile map p with
  | .error reason => .error reason
  | .ok target => .ok ⟨p, target, success⟩

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Identification
