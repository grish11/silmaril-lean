module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Weakening.Guarded.Defs

/-! Context embeddings factored into typed permutations and fresh unused slots. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding

open CategoryTheory
open SeaOfNodes.Diamond (ValueSort dataPorts sortValue Val)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.Loop.MLIR.CF (model)
open Silmaril.MLIR.Arith (Width)
open RVSDG (Port Tuple)
open Tail.Diamond.MLIR.CF.Pruned.Reindex (Permutation)
open SCCP.Dispatch (Checked Refusal)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (Admitted admit)
open Reindex.Guarded.Institution (AdmittedAt Generated Valuation)
open Reindex.Guarded.Institution renaming Signature → EntrySignature

/-- A typed factorization of an entry embedding. Different factorizations
may denote the same map on old ports. -/
inductive Embedding : EntrySignature → EntrySignature → Type where
  | id (S : EntrySignature) : Embedding S S
  | permute {S T U : EntrySignature} (order : S ⟶ T) (rest : Embedding T U) : Embedding S U
  | weaken {S T : EntrySignature} (fresh : ValueSort Width)
      (rest : Embedding (Weakening.Guarded.extend S fresh) T) : Embedding S T

/-- Read the selected feedback occurrence of an admitted program. -/
def selectedSide {S : EntrySignature} {result : Width} (p : AdmittedAt S result) : Bool :=
  @Checked.side _ _ _ _ model _ S.bankEq _ (@Admitted.checked _ _ S.bankEq p)

namespace Embedding

variable {S T : EntrySignature} {result : Width}

def rename (order : S ⟶ T) : Embedding S T :=
  .permute order (.id T)

def front (S : EntrySignature) (fresh : ValueSort Width) :
    Embedding S (Weakening.Guarded.extend S fresh) :=
  .weaken fresh (.id _)

/-- Apply the first embedding, then the second. -/
def trans : {S T U : EntrySignature} → Embedding S T → Embedding T U → Embedding S U
  | _, _, _, .id _, second => second
  | _, _, _, .permute order rest, second => .permute order (rest.trans second)
  | _, _, _, .weaken fresh rest, second => .weaken fresh (rest.trans second)

def portMap : {S T : EntrySignature} → Embedding S T → (t : SeaOfNodes.Diamond.Ty Width) →
    Port (dataPorts S.regs) t → Port (dataPorts T.regs) t
  | _, _, .id _, _, port => port
  | _, _, .permute order rest, t, port => rest.portMap t (order t port)
  | _, _, .weaken _ rest, t, port => rest.portMap t (.tail port)

/-- Read the target valuation in the original order and forget every inserted slot. -/
def reduct : {S T : EntrySignature} → Embedding S T → Valuation T → Valuation S
  | _, _, .id _, input => input
  | _, _, .permute order rest, input => Reindex.Guarded.Institution.reduct order (rest.reduct input)
  | _, _, .weaken _ rest, input => Weakening.project (rest.reduct input)

def mapAdmitted : {S T : EntrySignature} → Embedding S T → AdmittedAt S result → AdmittedAt T result
  | _, _, .id _, p => p
  | _, _, .permute order rest, p => rest.mapAdmitted (Reindex.Guarded.Institution.mapAdmitted order p)
  | _, _, .weaken fresh rest, p => rest.mapAdmitted (Weakening.Guarded.lift fresh p)

def mapGenerated : {S T : EntrySignature} → Embedding S T → Generated S result → Generated T result
  | _, _, .id _, p => p
  | _, _, .permute order rest, p => rest.mapGenerated (p.map order)
  | _, _, .weaken fresh rest, p => rest.mapGenerated (Weakening.Guarded.liftGenerated fresh p)

/-- Run the existing FIFO checker at the final signature. Intermediate
steps transport admission evidence. -/
def replay (path : Embedding S T) (p : AdmittedAt S result) : Except Refusal (AdmittedAt T result) :=
  let target := path.mapAdmitted p
  @admit _ _ T.bankEq (@Admitted.source _ _ T.bankEq target) (@Admitted.facts _ _ T.bankEq target)

/-- Replay once and invoke the existing guarded emitters on the final typed bank. -/
def compile (path : Embedding S T) (p : AdmittedAt S result) : Except Refusal (Generated T result) :=
  (path.replay p).map Generated.lower

end Embedding

/-- Move the new front slot to the requested position by adjacent swaps. -/
def insertionOrder (fresh : ValueSort Width) : (regs : List (ValueSort Width)) →
    (pos : Fin (regs.length + 1)) →
    Reindex.Registers (fresh :: regs) (regs.insertIdx pos.val fresh)
  | [], pos => Fin.cases (motive := fun i =>
      Reindex.Registers [fresh] (([] : List (ValueSort Width)).insertIdx i.val fresh))
      (Permutation.refl _) (fun i => i.elim0) pos
  | sort :: rest, pos => Fin.cases (motive := fun i =>
      Reindex.Registers (fresh :: sort :: rest) ((sort :: rest).insertIdx i.val fresh))
      (Permutation.refl _)
      (fun i => show Reindex.Registers (fresh :: sort :: rest) (sort :: rest.insertIdx i.val fresh) from
        Permutation.trans (Permutation.swap (T := SeaOfNodes.Diamond.Ty Width)
          (.value fresh) (.value sort) (dataPorts rest))
          (Permutation.cons (insertionOrder fresh rest i) (.value sort))) pos

def insertSignature (S : EntrySignature) (fresh : ValueSort Width) (pos : Fin (S.regs.length + 1)) :
    EntrySignature :=
  { regs := S.regs.insertIdx pos.val fresh }

/-- An ordinary insertion uses a zero-based index, including the position
after the last old register. -/
def insert (S : EntrySignature) (fresh : ValueSort Width) (pos : Fin (S.regs.length + 1)) :
    Embedding S (insertSignature S fresh pos) :=
  .weaken fresh (.rename (insertionOrder fresh S.regs pos))

/-- Build the target valuation with the same old values and the given capture. -/
def insertValue {S : EntrySignature} (fresh : ValueSort Width) (pos : Fin (S.regs.length + 1))
    (value : sortValue Word fresh) (input : Valuation S) : Valuation (insertSignature S fresh pos) :=
  Reindex.push (F := Val Word) (insertionOrder fresh S.regs pos) (Tuple.cons (F := Val Word) (t := .value fresh) value input)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding
