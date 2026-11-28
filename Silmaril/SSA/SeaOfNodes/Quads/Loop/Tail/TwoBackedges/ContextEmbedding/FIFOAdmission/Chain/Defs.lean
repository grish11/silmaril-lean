module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Composition.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission.Thms

/-! Follow a finite sequence of guarded capture checks and keep the real stage evidence. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op)
open Silmaril.MLIR.Arith (Width)
open Composition (thenMap)
open Identification (PortMap checkWrites program)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (Admitted)
open Reindex.Guarded.Institution (AdmittedAt Generated)
open Reindex.Guarded.Institution renaming Signature → EntrySignature

/-- Each map consumes the exact typed signature produced by its predecessor. -/
inductive CaptureChain : EntrySignature → EntrySignature → Type where
  | nil (S : EntrySignature) : CaptureChain S S
  | cons {S T U : EntrySignature} (head : PortMap S T) (tail : CaptureChain T U) : CaptureChain S U

namespace CaptureChain

variable {S T U : EntrySignature} {result : Width} {out : ValueSort Width}

def length : {S T : EntrySignature} → CaptureChain S T → Nat
  | _, _, .nil _ => 0
  | _, _, .cons _ tail => tail.length + 1

def append : {S T U : EntrySignature} → CaptureChain S T → CaptureChain T U → CaptureChain S U
  | _, _, _, .nil _, right => right
  | _, _, _, .cons head tail, right => .cons head (tail.append right)

def composite : {S T : EntrySignature} → CaptureChain S T → PortMap S T
  | _, _, .nil _ => fun _ port => port
  | _, _, .cons head tail => thenMap head tail.composite

/-- Check every map on the full bank reached by raw program transport.
This can inspect a suffix even when its input program failed FIFO admission. -/
def checkAllWrites : {S T : EntrySignature} → CaptureChain S T → Program Op S.regs out → Bool
  | _, _, .nil _, _ => true
  | _, _, .cons head tail, body =>
    checkWrites head body && tail.checkAllWrites (program head body)

/-- A failed stage retains the actual compiler outcome and diagnostic. -/
structure FailedStage (map : PortMap S T) (seed : AdmittedAt S result) where
  detail : Refusal T result
  diagnosed : diagnose map seed = .error detail
  rejected : Identification.compile map seed = .error detail.reason

/-- Every passed stage carries the actual emitted artifacts and their
compiler equation. At the first refusal only the remaining maps are retained. -/
inductive Report {result : Width} : {S T : EntrySignature} → CaptureChain S T → AdmittedAt S result → Type where
  | done {S : EntrySignature} (seed : AdmittedAt S result) : Report (.nil S) seed
  | passed {S T U : EntrySignature} {map : PortMap S T} {tail : CaptureChain T U}
      {seed : AdmittedAt S result} (emitted : Generated T result)
      (checked : Identification.compile map seed = .ok emitted)
      (rest : Report tail emitted.source) : Report (.cons map tail) seed
  | stopped {S T U : EntrySignature} {map : PortMap S T} {tail : CaptureChain T U}
      {seed : AdmittedAt S result} (failure : FailedStage map seed) : Report (.cons map tail) seed

private theorem refusal_matches (map : PortMap S T) (seed : AdmittedAt S result)
    (reason : Identification.Refusal) (rejected : Identification.compile map seed = .error reason) :
    (diagnose map seed).mapError Refusal.reason = .error reason := by
  rw [diagnose_compile, rejected]
  rfl

/-- Recover the typed diagnostic for an actual refused compiler call. -/
def FailedStage.ofError (map : PortMap S T) (seed : AdmittedAt S result)
    (reason : Identification.Refusal) (rejected : Identification.compile map seed = .error reason) :
    FailedStage map seed :=
  match found : diagnose map seed with
  | .error detail =>
    have agrees : detail.reason = reason := by
      have same := refusal_matches map seed reason rejected
      rw [found] at same
      exact Except.error.inj same
    ⟨detail, found, agrees ▸ rejected⟩
  | .ok value =>
    have impossible : (Except.ok value : Except Identification.Refusal Unit) = .error reason := by
      simpa only [found, Except.mapError] using refusal_matches map seed reason rejected
    nomatch impossible

/-- Run the existing compiler at each stage until the first refusal.
The diagnostic is computed only for that refused call. -/
def run : {S T : EntrySignature} → (chain : CaptureChain S T) → (seed : AdmittedAt S result) → Report chain seed
  | _, _, .nil _, seed => .done seed
  | _, _, .cons head tail, seed =>
    match checked : Identification.compile head seed with
    | .ok emitted => .passed emitted checked (tail.run emitted.source)
    | .error reason => .stopped (FailedStage.ofError head seed reason checked)

/-- A compact view with the zero-based index of the first failed call. -/
def Report.firstFailure : {S T : EntrySignature} → {chain : CaptureChain S T} → {seed : AdmittedAt S result} →
    Report chain seed → Option (Nat × Identification.Refusal)
  | _, _, _, _, .done _ => none
  | _, _, _, _, .passed _ _ rest => rest.firstFailure.map (fun (i, reason) => (i + 1, reason))
  | _, _, _, _, .stopped failed => some (0, failed.detail.reason)

/-- The actual last emission if every stage passed and the chain was nonempty. -/
def Report.lastArtifact : {S T : EntrySignature} → {chain : CaptureChain S T} → {seed : AdmittedAt S result} →
    Report chain seed → Option (Generated T result)
  | _, _, _, _, .done _ => none
  | _, _, _, _, .passed emitted _ (.done _) => some emitted
  | _, _, _, _, .passed _ _ rest => rest.lastArtifact
  | _, _, _, _, .stopped _ => none

end CaptureChain
end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission
