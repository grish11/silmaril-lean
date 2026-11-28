module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.LiftComposition.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Composition.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FactTransport.Coverage

/-! The second and one-shot compilers use the same final program and facts. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FactTransport.Proofs

open Silmaril.MLIR.Arith (Width)
open Composition (thenMap program_thenMap)
open Identification (PortMap checkWrites program pushFacts)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (Admitted)
open Reindex.Guarded.Institution (AdmittedAt Generated)
open Reindex.Guarded.Institution renaming Signature → EntrySignature

variable {S T U : EntrySignature} {result : Width}

theorem final_inputs_eq (first : PortMap S T) (second : PortMap T U)
    (p : AdmittedAt S result) (mid : Generated T result) (firstOk : Identification.compile first p = .ok mid) :
    (program second (@Admitted.source _ _ T.bankEq mid.source),
      pushFacts second (@Admitted.facts _ _ T.bankEq mid.source)) =
    (program (thenMap first second) (@Admitted.source _ _ S.bankEq p),
      pushFacts (thenMap first second) (@Admitted.facts _ _ S.bankEq p)) := by
  apply Prod.ext
  · change program second (@Admitted.source _ _ T.bankEq mid.source) = _
    rw [Identification.compile_source first p firstOk, program_thenMap]
  · change pushFacts second (@Admitted.facts _ _ T.bankEq mid.source) = _
    rw [pushFacts_comp, Identification.compile_facts first p firstOk]
    rfl

theorem second_compile_check (first : PortMap S T) (second : PortMap T U)
    (p : AdmittedAt S result) (mid : Generated T result) (firstOk : Identification.compile first p = .ok mid) :
    Identification.compile second mid.source =
      if checkWrites second (@Admitted.source _ _ T.bankEq mid.source) then
        Identification.compile (thenMap first second) p
      else .error .aliasedWrite := by
  by_cases checked : checkWrites second (@Admitted.source _ _ T.bankEq mid.source) = true
  · have stageSafe := (Identification.checkWrites_iff _ _).mp checked
    rw [Identification.compile_source first p firstOk] at stageSafe
    have directSafe := Composition.safeWrites_thenMap first second _
      (Identification.compile_safe first p firstOk) stageSafe
    have directChecked := (Identification.checkWrites_iff _ _).mpr directSafe
    have inputs := final_inputs_eq first second p mid firstOk
    have code : program second (@Admitted.source _ _ T.bankEq mid.source) =
        program (thenMap first second) (@Admitted.source _ _ S.bankEq p) := congrArg Prod.fst inputs
    have facts : pushFacts second (@Admitted.facts _ _ T.bankEq mid.source) =
        pushFacts (thenMap first second) (@Admitted.facts _ _ S.bankEq p) := congrArg Prod.snd inputs
    simp only [Identification.compile, Identification.replay, checked, directChecked, ite_true, code, facts]
  · simp [Identification.compile, Identification.replay, checked, Except.map]

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FactTransport.Proofs
