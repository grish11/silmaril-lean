module

public import Silmaril.Process.ITreeTrace.Defs
public import Silmaril.Semantics.ITree.Trace.Thms

public section

namespace Silmaril.Process.ITreeTrace.Proofs

open TypedSyscall (Signature Kernel)
open Silmaril.Elgot.ITree

variable {sig : Signature} {Tid A S Label Obs Other : Type} [DecidableEq Tid]

theorem relabel_iff {kernel : Kernel sig S Label} {observe : Tid → Label → Obs}
    (project : Obs → Other) {schedule : List Tid} {pool : Pool sig Tid A} {before after : S}
    {trace : List Other} {stop : End sig Tid A} :
    Flatten kernel (fun tid label => project (observe tid label)) schedule pool before trace stop after ↔
      ∃ full, Flatten kernel observe schedule pool before full stop after ∧ full.map project = trace := by
  constructor
  · intro run
    induction run with
    | returned done => exact ⟨[], .returned done, rfl⟩
    | exhausted live => exact ⟨[], .exhausted live, rfl⟩
    | silent root => exact ⟨[], .silent root, rfl⟩
    | blocked root pending => exact ⟨[], .blocked root pending, rfl⟩
    | exited root step => exact ⟨[_], .exited root step, rfl⟩
    | exchange root step _ ih =>
        obtain ⟨full, tail, rfl⟩ := ih
        exact ⟨_ :: full, .exchange root step tail, rfl⟩
    | skip root live _ ih =>
        obtain ⟨full, tail, rfl⟩ := ih
        exact ⟨full, .skip root live tail, rfl⟩
  · rintro ⟨full, run, rfl⟩
    induction run with
    | returned done => exact .returned done
    | exhausted live => exact .exhausted live
    | silent root => exact .silent root
    | blocked root pending => exact .blocked root pending
    | exited root step => exact .exited root step
    | exchange root step _ ih => exact .exchange root step ih
    | skip root live _ ih => exact .skip root live ih

private def visibleRequest : Visible (Event sig) A (Program sig A) → Option sig.Request
  | .ret _ => none
  | .vis (.call req) _ => some req

theorem allows_ret (a : A) (permitted : sig.Request → Prop) :
    Allows (ret a : Program sig A) permitted := by
  intro trace has
  cases trace with
  | «prefix» => trivial
  | result _ => trivial
  | request event => simp [HasTrace] at has
  | exchange event reply tail => simp [HasTrace] at has

theorem allows_vis {permitted : sig.Request → Prop} {req : sig.Request}
    {next : sig.Response req → Program sig A} (allowed : permitted req)
    (tailAllowed : ∀ reply, Allows (next reply) permitted) :
    Allows (vis (.call req) next) permitted := by
  intro trace has
  cases trace with
  | «prefix» => trivial
  | result a => simp [HasTrace] at has
  | request event =>
      cases event with
      | call requested =>
          obtain ⟨_, root⟩ := has
          have same := congrArg visibleRequest (Part.some_inj.mp ((out_vis _ _).symm.trans root))
          change some req = some requested at same
          have eq := Option.some.inj same
          subst requested
          exact allowed
  | exchange event reply tail =>
      cases event with
      | call requested =>
          have witness := has
          obtain ⟨_, root, _⟩ := witness
          have same := congrArg visibleRequest (Part.some_inj.mp ((out_vis _ _).symm.trans root))
          change some req = some requested at same
          have eq := Option.some.inj same
          subst requested
          exact ⟨allowed, tailAllowed reply tail ((hasTrace_vis_exchange_iff _ _ _ _).mp has)⟩

end Silmaril.Process.ITreeTrace.Proofs
