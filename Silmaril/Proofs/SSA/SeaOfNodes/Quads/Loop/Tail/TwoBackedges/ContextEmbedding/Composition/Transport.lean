module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Composition.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Identification.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Thms

/-! Typed composition for values and syntax, and its write-fibre check. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Composition.Proofs

open SeaOfNodes.Diamond (ValueSort dataPorts)
open SeaOfNodes.Loop.MLIR.CF (Op)
open Silmaril.MLIR.Arith (Width)
open RVSDG (Port Tuple)
open Identification (BankMap PortMap pull reduct quad program quads SafeWrites)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (Admitted)
open Reindex.Guarded.Institution (AdmittedAt Valuation)
open Reindex.Guarded.Institution renaming Signature → EntrySignature

variable {old middle new : List (ValueSort Width)} {out : ValueSort Width}
variable {S T U : EntrySignature}

theorem pull_thenMap {F : SeaOfNodes.Diamond.Ty Width → Type}
    (first : BankMap old middle) (second : BankMap middle new) (value : Tuple F (dataPorts new)) :
    pull (thenMap first second) value = pull first (pull second value) := by
  unfold pull
  apply congrArg (tabulate (dataPorts old))
  funext sort port
  rw [get_tabulate]
  rfl

theorem reduct_embedding (first : PortMap S T) (second : Embedding T U) (input : Valuation U) :
    reduct (thenMap first second.portMap) input = reduct first (second.reduct input) := by
  change pull (thenMap first second.portMap) input = pull first (second.reduct input)
  rw [pull_thenMap]
  exact congrArg (pull first) (Identification.reduct_embedding second input)

private theorem map_operands (first : BankMap old middle) (second : BankMap middle new)
    {args : List (SeaOfNodes.Diamond.Ty Width)} (operands : Tuple (Port (dataPorts old)) args) :
    (operands.map first).map second = operands.map (thenMap first second) := by
  induction operands with
  | nil => rfl
  | cons head rest ih => exact congrArg (Tuple.cons (second _ (first _ head))) ih

private theorem quad_thenMap (first : BankMap old middle) (second : BankMap middle new)
    (q : Quad Op old) :
    quad second (quad first q) = quad (thenMap first second) q := by
  cases q
  simp only [quad, thenMap]
  rw [map_operands]

theorem program_thenMap (first : BankMap old middle) (second : BankMap middle new)
    (p : Program Op old out) :
    program second (program first p) = program (thenMap first second) p := by
  simp only [program, List.map_map, Function.comp_def, quad_thenMap, thenMap]

theorem safeWrites_of_thenMap (first : BankMap old middle) (second : BankMap middle new)
    (p : Program Op old out) (safe : SafeWrites (thenMap first second) p) : SafeWrites first p := by
  intro q present sort port shared
  obtain ⟨rfl, equal⟩ := Sigma.mk.inj_iff.mp (Reindex.slot_eq _ _ shared)
  exact safe q present _ port (congrArg (fun r => slot (second _ r)) (eq_of_heq equal))

theorem safeWrites_thenMap (first : BankMap old middle) (second : BankMap middle new)
    (p : Program Op old out) (firstSafe : SafeWrites first p)
    (secondSafe : SafeWrites second (program first p)) : SafeWrites (thenMap first second) p := by
  intro q present sort port shared
  have mapped : quad first q ∈ quads (program first p) := by
    simpa only [quads, program, List.map_append] using List.mem_map_of_mem (f := quad first) present
  exact firstSafe q present sort port (secondSafe (quad first q) mapped sort (first sort port) shared)

theorem checkWrites_embedding (first : PortMap S T) (second : Embedding T U)
    (p : Program Op S.regs out) :
    Identification.checkWrites (thenMap first second.portMap) p = Identification.checkWrites first p := by
  apply Bool.eq_iff_iff.mpr
  simp only [Identification.checkWrites_iff]
  exact ⟨safeWrites_of_thenMap first second.portMap p,
    fun safe => safeWrites_thenMap first second.portMap p safe
      (Identification.embedding_safe second (program first p))⟩

private theorem quad_identity (q : Quad Op old) : quad (fun _ port => port) q = q := by
  have operandsId {args} (operands : Tuple (Port (dataPorts old)) args) :
      operands.map (fun _ port => port) = operands := by
    induction operands with
    | nil => rfl
    | cons head _ ih => exact congrArg (Tuple.cons head) ih
  cases q
  simp only [quad, operandsId]

theorem embedding_source (path : Embedding S T) {result : Width} (p : AdmittedAt S result) :
    @Admitted.source _ _ T.bankEq (path.mapAdmitted p) =
      program path.portMap (@Admitted.source _ _ S.bankEq p) := by
  induction path with
  | id S =>
    change @Admitted.source _ _ S.bankEq p = program (fun _ port => port) (@Admitted.source _ _ S.bankEq p)
    generalize @Admitted.source _ _ S.bankEq p = source
    cases source
    have identity : (quad (fun _ port => port) : Quad Op S.regs → Quad Op S.regs) = id :=
      funext quad_identity
    simp [program, identity]
  | permute order rest ih =>
    rw [Embedding.mapAdmitted, ih]
    exact program_thenMap (fun t => order t) rest.portMap _
  | weaken fresh rest ih =>
    rw [Embedding.mapAdmitted, ih]
    exact program_thenMap (middle := fresh :: _) (fun _ port => .tail port) rest.portMap _

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Composition.Proofs
