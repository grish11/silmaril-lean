module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FactTransport.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Composition.Thms
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.LiftComposition.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FactTransport.Coverage
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FactTransport.Compile
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FactTransport.Fibres

/-! Exact composition of typed intersections and of the final guarded checker inputs. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FactTransport

open SeaOfNodes.Diamond (ValueSort dataPorts)
open SeaOfNodes.Diamond.SCCP (TupleCovers TupleLE)
open SeaOfNodes.Loop.MLIR.CF (model)
open Silmaril.MLIR.Arith (Width)
open Blocks (Bank)
open RVSDG (Port)
open Identification (BankMap PortMap checkWrites program pushFacts)
open Composition (thenMap)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (Admitted EntryFacts)
open Reindex.Guarded.Institution (AdmittedAt Generated)
open Reindex.Guarded.Institution renaming Signature → EntrySignature

variable {old middle new : List (ValueSort Width)}
variable {S T U : EntrySignature} {result : Width}

/-- Any returned fact block covers at least one valuation. -/
theorem pushFacts_has_cover (map : BankMap old new) (facts : EntryFacts old) (out : EntryFacts new)
    (pushed : pushFacts map facts = some out) : ∃ input : Bank (regs := new) model, TupleCovers out input :=
  Proofs.pushFacts_has_cover map facts out pushed

theorem pushFacts_refines (map : BankMap old new) (facts : EntryFacts old) (out : EntryFacts new)
    (pushed : pushFacts map facts = some out) : TupleLE (Identification.pull map out) facts :=
  Proofs.pushFacts_refines map facts out pushed

theorem pushFacts_compatible_iff (map : BankMap old new) (facts : EntryFacts old) :
    (pushFacts map facts).isSome ↔ Compatible map facts :=
  Proofs.pushFacts_compatible_iff map facts

/-- A target coordinate with an empty fibre keeps the initial overdefined fact. -/
theorem pushFacts_unused (map : BankMap old new) (facts : EntryFacts old) (out : EntryFacts new)
    {t : SeaOfNodes.Diamond.Ty Width} (target : Port (dataPorts new) t)
    (unused : ¬ ∃ origin, map t origin = target) (ok : pushFacts map facts = some out) :
    out.get target = .overdefined :=
  Proofs.pushFacts_unused map facts out target unused ok

/-- Two typed intersections agree exactly after composition, including a refusal.
Both maps may identify ports. -/
theorem pushFacts_comp (first : BankMap old middle) (second : BankMap middle new) (facts : EntryFacts old) :
    pushFacts (thenMap first second) facts = (pushFacts first facts).bind (pushFacts second) :=
  Proofs.pushFacts_comp first second facts

/-- A successful intermediate compilation gives identical final programs
and optional fact blocks by the two routes. -/
theorem final_inputs_eq (first : PortMap S T) (second : PortMap T U)
    (p : AdmittedAt S result) (mid : Generated T result) (firstOk : Identification.compile first p = .ok mid) :
    (program second (@Admitted.source _ _ T.bankEq mid.source),
      pushFacts second (@Admitted.facts _ _ T.bankEq mid.source)) =
    (program (thenMap first second) (@Admitted.source _ _ S.bankEq p),
      pushFacts (thenMap first second) (@Admitted.facts _ _ S.bankEq p)) :=
  Proofs.final_inputs_eq first second p mid firstOk

/-- When a final fact block exists, the actual FIFO solves the same program
with the same entry facts at the final signature. -/
theorem final_fifo_eq (first : PortMap S T) (second : PortMap T U)
    (p : AdmittedAt S result) (mid : Generated T result) (firstOk : Identification.compile first p = .ok mid) :
    (pushFacts second (@Admitted.facts _ _ T.bankEq mid.source)).map
      (@SCCP.Worklist.solve _ _ _ _ model (program second (@Admitted.source _ _ T.bankEq mid.source)) U.bankEq) =
    (pushFacts (thenMap first second) (@Admitted.facts _ _ S.bankEq p)).map
      (@SCCP.Worklist.solve _ _ _ _ model (program (thenMap first second) (@Admitted.source _ _ S.bankEq p)) U.bankEq) :=
  congrArg (fun inputs => inputs.2.map (@SCCP.Worklist.solve _ _ _ _ model inputs.1 U.bankEq))
    (final_inputs_eq first second p mid firstOk)

/-- After first admission, only the second write check can prevent the
staged compiler from using the same final checker and emitter. -/
theorem second_compile_check (first : PortMap S T) (second : PortMap T U)
    (p : AdmittedAt S result) (mid : Generated T result) (firstOk : Identification.compile first p = .ok mid) :
    Identification.compile second mid.source =
      if checkWrites second (@Admitted.source _ _ T.bankEq mid.source) then
        Identification.compile (thenMap first second) p
      else .error .aliasedWrite :=
  Proofs.second_compile_check first second p mid firstOk

theorem second_compile_eq (first : PortMap S T) (second : PortMap T U)
    (p : AdmittedAt S result) (mid : Generated T result) (firstOk : Identification.compile first p = .ok mid)
    (safe : checkWrites second (@Admitted.source _ _ T.bankEq mid.source) = true) :
    Identification.compile second mid.source = Identification.compile (thenMap first second) p := by
  simpa only [safe, ite_true] using second_compile_check first second p mid firstOk

/-- Successful comparisons contain identical stored final artifacts. -/
theorem compared_eq {first : PortMap S T} {second : PortMap T U}
    (pair : LiftComposition.Compared first second result) : pair.staged = pair.direct :=
  Except.ok.inj (pair.secondOk.symm.trans
    ((second_compile_eq first second pair.source pair.intermediate pair.firstOk
      ((Identification.checkWrites_iff _ _).mpr (Identification.compile_safe second _ pair.secondOk))).trans pair.directOk))

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FactTransport
