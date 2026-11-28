module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Weakening.Thms
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Guarded.Institution.Defs

/-! Replay and emit an admitted guarded program with an unused typed capture. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Weakening.Guarded

open SeaOfNodes.Diamond (ValueSort sortValue)
open SeaOfNodes.Loop.MLIR.CF (model)
open SeaOfNodes.MLIR (Word)
open Silmaril.MLIR.Arith (Width)
open SCCP.Dispatch (Checked Refusal)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (Admitted admit)
open Reindex.Guarded.Institution (AdmittedAt Generated decidableBank)
open Reindex.Guarded.Institution renaming Signature → EntrySignature

variable {S : EntrySignature} {result : Width}

def captureEq (fresh : ValueSort Width) : DecidableEq (sortValue Word fresh) :=
  (decidableBank [fresh]).atPort (0 : Fin 1)

/-- A local signature extension. The old bank keeps its equality dictionary. -/
def extend (S : EntrySignature) (fresh : ValueSort Width) : EntrySignature :=
  ⟨fresh :: S.regs, extendEq (captureEq fresh) S.bankEq⟩

/-- The source and its enlarged entry facts go through the existing FIFO checker. -/
def replay (fresh : ValueSort Width) (p : AdmittedAt S result) :
    Except Refusal (AdmittedAt (extend S fresh) result) := by
  letI := S.bankEq
  exact @admit _ _ (extend S fresh).bankEq (program fresh p.source) (facts fresh p.facts)

/-- Transport singleton evidence using the projected least solution.
The record carries a proof of admission by the actual checker. -/
def lift (fresh : ValueSort Width) (p : AdmittedAt S result) : AdmittedAt (extend S fresh) result := by
  letI := S.bankEq
  let source := program fresh p.source
  let contract := facts fresh p.facts
  have marks := congrArg Prod.fst (solve_project model p.source (captureEq fresh) p.facts)
  let equality := (extend S fresh).bankEq
  let certificate := @Checked.mk _ _ _ _ model source equality contract
    p.checked.side (marks.symm ▸ p.checked.marked) (marks.symm ▸ p.checked.excluded)
  exact @Admitted.mk _ _ equality source contract certificate
    (by exact @Reindex.Guarded.fifo_accepts _ _ _ _ model equality source contract certificate)

/-- Re-run admission then use the existing guarded emitters. -/
def compile (fresh : ValueSort Width) (p : AdmittedAt S result) :
    Except Refusal (Generated (extend S fresh) result) :=
  (replay fresh p).map Generated.lower

def liftGenerated (fresh : ValueSort Width) (p : Generated S result) :
    Generated (extend S fresh) result :=
  Generated.lower (lift fresh p.source)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Weakening.Guarded
