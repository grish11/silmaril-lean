module

public import Silmaril.Process.ITreeTrace.Defs
public import Silmaril.Semantics.ITree.Trace.Thms
public import Mathlib.Logic.Small.Basic
import Silmaril.Proofs.Process.ITreeTrace.Flatten
import Silmaril.Proofs.Process.ITreeTrace.Small

public section

namespace Silmaril.Process.ITreeTrace

open TypedSyscall (Signature Kernel)
open Silmaril.Elgot.ITree (out ret vis)

instance (sig : Signature) (A : Type) : Small.{0} (Program sig A) :=
  Proofs.smallProgram sig A

variable {sig : Signature} {Tid A S Label Obs Other : Type} [DecidableEq Tid]

/-- Project the realized labels without changing kernel choices, stores or the endpoint. -/
theorem Flatten.relabel_iff {kernel : Kernel sig S Label} {observe : Tid → Label → Obs}
    (project : Obs → Other) {schedule : List Tid} {pool : Pool sig Tid A} {before after : S}
    {trace : List Other} {stop : End sig Tid A} :
    Flatten kernel (fun tid label => project (observe tid label)) schedule pool before trace stop after ↔
      ∃ full, Flatten kernel observe schedule pool before full stop after ∧ full.map project = trace :=
  Proofs.relabel_iff project

/-- Singleton lifting preserves and reflects every realized sequential result,
including its final store and stopping reason, after erasing thread tags. -/
theorem sequential_iff_singleton {kernel : Kernel sig S Label} {fuel : Nat} {prog : Program sig A}
    {before after : S} {trace : List Label} {stop : End sig Unit A} :
    Sequential kernel fuel prog before trace stop after ↔
      ∃ tagged, Interleaving kernel (List.replicate fuel ()) (singleton prog) before tagged stop after ∧
        tagged.map Prod.snd = trace :=
  Flatten.relabel_iff (observe := fun (tid : Unit) (label : Label) => (tid, label)) Prod.snd

theorem allows_ret (a : A) (permitted : sig.Request → Prop) :
    Allows (ret a : Program sig A) permitted :=
  Proofs.allows_ret a permitted

theorem allows_vis {permitted : sig.Request → Prop} {req : sig.Request}
    {next : sig.Response req → Program sig A} (allowed : permitted req)
    (tailAllowed : ∀ reply, Allows (next reply) permitted) :
    Allows (vis (.call req) next) permitted :=
  Proofs.allows_vis allowed tailAllowed

/-- A visible request of an allowed tree is permitted, and each reply continues safely. -/
theorem Allows.atCall {permitted : sig.Request → Prop} {prog : Program sig A} {req : sig.Request}
    {next : sig.Response req → Program sig A} (safe : Allows prog permitted)
    (root : out prog = Part.some (.vis (.call req) next)) :
    permitted req ∧ ∀ reply, Allows (next reply) permitted :=
  ⟨safe (.request (.call req)) ⟨next, root⟩,
    fun reply trace has => (safe (.exchange (.call req) reply trace) ⟨next, root, has⟩).2⟩

end Silmaril.Process.ITreeTrace
