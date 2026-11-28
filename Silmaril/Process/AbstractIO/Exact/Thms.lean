module

public import Silmaril.Process.AbstractIO.Exact.Defs
public import Silmaril.Process.ITreeTrace.Exact.Thms
import Silmaril.Proofs.Process.AbstractIO.Exact.API

public section

namespace Silmaril.Process.AbstractIO.Exact

open Silmaril.Elgot.ITree (ret trigger vis)
open Silmaril.Elgot.ITree.Exact (Kernel Observes Satisfies Step Finish)
open ITreeTrace (Event)
open ITreeTrace.Exact (lowering)

theorem lower_positionedCopy (src dst : FilePosition) (count : Nat) :
    (lowering positionedCalls).lower (positionedCopy src dst count) =
      fileAPI.map (trigger (Event.call (sig := fileSignature) (.copyChunk src dst count))) :=
  Proofs.lower_positionedCopy src dst count

theorem lower_network_call (req : NetworkRequest) :
    (lowering networkCalls).lower (trigger (Event.call (sig := networkSignature) req)) =
      networkAPI.map (trigger (Event.call (sig := networkSignature) req)) :=
  Proofs.lower_network_call req

/-- The institution's satisfaction condition for the actual positioned-file API handler. -/
theorem copy_satisfies_iff (src dst : FilePosition) (count : Nat) (pre : Store → Prop)
    (post : Store → Silmaril.Elgot.ITree.Exact.Observation profile (IOResult Nat) → Prop) :
    (∀ before, pre before → ∀ obs,
      Observes linuxKernel ()
        (fileAPI.map (trigger (Event.call (sig := fileSignature) (.copyChunk src dst count))), before) obs →
      post before obs) ↔
    Satisfies (Kernel.reduct (lowering positionedCalls) linuxKernel)
      (copySentence src dst count pre post) :=
  Proofs.copy_satisfies_iff src dst count pre post

/-- A visible completion uses an actual abstract I/O transition and emits its typed exchange. -/
theorem call_step_iff {A : Type} {req : signature.Request} {before after : Store}
    {batch : List Observation} {next : signature.Response req → Prog A} {tree : Prog A} :
    Step linuxKernel () (vis (Event.call (sig := signature) req) next, before) batch (tree, after) ↔
      ∃ choice, batch = [⟨req, (step choice before req).1⟩] ∧
        after = (step choice before req).2 ∧ tree = next (step choice before req).1 :=
  Proofs.call_step_iff

/-- The abstract nonblocking kernel always replies. A terminal observation requires a tree return. -/
theorem finish_iff {A : Type} {prog : Prog A} {before : Store} {batch : List Observation}
    {last : Silmaril.Elgot.ITree.Exact.End profile A} :
    Finish linuxKernel () (prog, before) batch last ↔
      ∃ value, prog = ret value ∧ batch = [] ∧ last = .returned value before :=
  Proofs.finish_iff

end Silmaril.Process.AbstractIO.Exact
