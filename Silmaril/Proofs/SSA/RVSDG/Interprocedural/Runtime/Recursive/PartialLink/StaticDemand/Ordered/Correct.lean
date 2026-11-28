module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Defs
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Family.Wrapper.Correct

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Proofs

open NestedTheta.Liveness (Demand)
open Continuation.Partial.Executable (Actions)
open StaticDemand.Proofs (MemberDispatch family_dispatch lambda_with_dispatch prefix_observes)

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {table : MemberSummaries V S} {imports exports final : Ports (Ty V S)}
variable {past sigs : List (Ports (Ty V S))} {fn : Function V S} {actions : Actions m σ}

private theorem dispatches (earlier : Dispatch actions table) (observed : Demand) (budget : Nat) :
    MemberDispatch actions observed earlier.left earlier.right budget final := by
  intro depth _ i
  dsimp only
  intro wanted fL fR capsL capsR argsL argsR store left right hL hR live resume
  exact earlier.transport i fL fR capsL capsR hL hR observed wanted depth argsL argsR store left right
    (fun p needed => live (.arg p) needed) (fun l r s h => resume l r s h trivial trivial)

theorem seed_transport (family : StaticDemand.Family Op table imports)
    (groupL groupR : Tuple m.Val family.context)
    (readyL : family.Ready groupL) (readyR : family.Ready groupR) :
    ∀ i fL fR capsL capsR,
      family.guard groupL i fL capsL → family.guard groupR i fR capsR →
      CallAgrees actions (table.at i) fL fR capsL capsR := by
  intro i fL fR capsL capsR hL hR observed wanted depth final argsL argsR store left right live resume
  refine family_dispatch family actions observed groupL groupR readyL readyR depth (final := final)
    depth (Nat.le_refl _) i wanted fL fR capsL capsR argsL argsR store left right hL hR ?_ ?_
  · intro ty source needed
    cases source with
    | output j _ => exact j.elim0
    | arg p => exact live p needed
  · intro outL outR middle equal _ _
    exact resume outL outR middle equal

theorem lambda_transport (earlier : Dispatch actions table) (binding : Binding Op table imports past fn)
    {pastR : List (Ports (Ty V S))} (capturesR : Wires imports pastR binding.context)
    (inputsL inputsR : Tuple m.Val imports) (localsL : Locals m.Val past) (localsR : Locals m.Val pastR)
    (resolvedL : binding.resolved earlier.left inputsL localsL)
    (resolvedR : (binding.withCaptures capturesR).resolved earlier.right inputsR localsR) :
    ∀ i fL fR capsL capsR,
      binding.extendGuard earlier.left inputsL localsL i fL capsL →
      (binding.withCaptures capturesR).extendGuard earlier.right inputsR localsR i fR capsR →
      CallAgrees actions ((prepend binding.summary table).at i) fL fR capsL capsR := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · intro fL fR capsL capsR hL hR
    rcases hL with ⟨targetL, capL⟩
    rcases hR with ⟨targetR, capR⟩
    rw [targetL, targetR, capL, capR]
    intro observed wanted depth final argsL argsR store left right live resume
    apply lambda_with_dispatch binding.body actions observed wanted earlier.left earlier.right
      (fun n => dispatches earlier observed n) _ _ argsL argsR store left right depth
      (resolvedL argsL) (resolvedR argsR) live
    intro outL outR middle equal _ _
    exact resume outL outR middle equal
  · exact earlier.transport j

theorem linked (checked : Dispatch actions table) (i : Fin table.members.length)
    (demand : Demand) (fuel after unitId : Nat) (graph : Omega Op imports exports sigs)
    (port : Port exports (table.at i).fn.port)
    (inputsL inputsR : Tuple m.Val imports) (argsL argsR : Tuple m.Val (table.at i).fn.args) (initial : σ)
    {outsL outsR : Tuple m.Val exports} {middle : σ} {capsL capsR : Tuple m.Val (table.at i).captures}
    (linkedL : Executable.link actions unitId graph inputsL initial = .linked outsL middle)
    (linkedR : Executable.link actions unitId graph inputsR initial = .linked outsR middle)
    (dispatchL : checked.left i (outsL.get port) capsL) (dispatchR : checked.right i (outsR.get port) capsR)
    (agree : InputsAgree (m := m) (table.at i) demand (prependContext argsL capsL) (prependContext argsR capsR)) :
    ∃ left right,
      Executable.run actions fuel unitId graph inputsL port argsL initial = .ok left ∧
      Executable.run actions fuel unitId graph inputsR port argsR initial = .ok right ∧
      PrefixObservationsAgree actions demand after left right := by
  have matched := checked.transport i _ _ capsL capsR dispatchL dispatchR demand demand
    (fuel + after + 1) argsL argsR middle .halt .halt agree
    (fun _ _ _ h => PrefixMatches.returned h)
  have related := prefix_observes fuel after matched
  exact ⟨_, _, by simp only [Executable.run, Executable.start, linkedL, Except.map]; rfl,
    by simp only [Executable.run, Executable.start, linkedR, Except.map]; rfl, related⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Proofs
