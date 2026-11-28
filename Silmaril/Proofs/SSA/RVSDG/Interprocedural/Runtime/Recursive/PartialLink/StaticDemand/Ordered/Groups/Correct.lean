module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Groups.Defs
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Family.Correct

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Groups.Proofs

open Continuation.Partial.Executable (Actions)
open NestedTheta.Liveness (Demand)
open StaticDemand.Proofs (MemberDispatch MemberDispatchAt member_prefix_with)

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {actions : Actions m σ} {earlier later calls : MemberSummaries V S}
variable {imports exports : Ports (Ty V S)} {past sigs familyPast : List (Ports (Ty V S))}

private theorem transport {source target : MemberSummary V S} (same : source = target)
    (contract : (summary : MemberSummary V S) → SlotGuard m summary → SlotGuard m summary → Prop)
    (left right : SlotGuard m source) (sound : contract source left right) :
    contract target (same ▸ left) (same ▸ right) := by
  subst target
  exact sound

private theorem combine_slots (contract : (summary : MemberSummary V S) → SlotGuard m summary → SlotGuard m summary → Prop)
    (oldL oldR : Guard m earlier) (newL newR : Guard m later)
    (old : ∀ i, contract (earlier.at i) (oldL i) (oldR i))
    (new : ∀ i, contract (later.at i) (newL i) (newR i)) :
    ∀ i, contract ((append earlier later).at i) ((oldL.combine newL) i) ((oldR.combine newR) i) :=
  slotCases earlier later
    (result := fun i => contract ((append earlier later).at i) ((oldL.combine newL) i) ((oldR.combine newR) i))
    (fun j => by
      rw [Guard.combine_left, Guard.combine_left]
      exact transport (append_at_old earlier later j).symm contract _ _ (old j))
    (fun j => by
      rw [Guard.combine_right, Guard.combine_right]
      exact transport (append_at_new earlier later j).symm contract _ _ (new j))

theorem combine (old : Dispatch actions earlier) (new : Dispatch actions later) :
    ∀ i, DispatchAt actions ((append earlier later).at i) ((old.left.combine new.left) i)
      ((old.right.combine new.right) i) :=
  combine_slots (DispatchAt actions) old.left old.right new.left new.right old.transport new.transport

private theorem combine_budget (old : Dispatch actions earlier) (newL newR : Guard m later)
    (observed : Demand) (budget : Nat) (final : Ports (Ty V S))
    (new : MemberDispatch actions observed newL newR budget final) :
    MemberDispatch actions observed (old.left.combine newL) (old.right.combine newR) budget final := by
  intro depth bounded
  apply combine_slots (MemberDispatchAt actions observed depth final) old.left old.right newL newR
    (new := new depth bounded)
  intro i wanted fL fR capsL capsR argsL argsR store left right hL hR live resume
  exact old.transport i fL fR capsL capsR hL hR observed wanted depth argsL argsR store left right
    (fun p needed => live (.arg p) needed) (fun l r s h => resume l r s h trivial trivial)

theorem open_transport (old : Dispatch actions earlier)
    (family : StaticDemand.Family Op later imports (append earlier later) familyPast)
    (capturedL capturedR : Tuple m.Val family.context)
    (readyL : family.ReadyWith capturedL (old.left.combine (family.guard capturedL)))
    (readyR : family.ReadyWith capturedR (old.right.combine (family.guard capturedR))) :
    ∀ i, DispatchAt actions (later.at i) (family.guard capturedL i) (family.guard capturedR i) := by
  intro i fL fR capsL capsR hL hR observed wanted depth final argsL argsR store left right live resume
  rcases hL with ⟨targetL, valuesL⟩
  rcases hR with ⟨targetR, valuesR⟩
  rw [targetL, targetR]
  rw [valuesL, valuesR] at live
  apply member_prefix_with family actions observed capturedL capturedR _ _ readyL readyR
    (fun n => combine_budget old _ _ observed n final) depth i wanted argsL argsR store left right
  · intro ty source needed
    cases source with
    | output j _ => exact j.elim0
    | arg p => exact live p needed
  · intro l r s h _ _
    exact resume l r s h

private theorem atSlot {table : MemberSummaries V S} {guard : Guard m table}
    (i : Fin table.members.length) {source : MemberSummary V S}
    (same : source = table.at i) (test : SlotGuard m source)
    (reads : guard i = (same ▸ test)) (f : m.Val source.fn.port)
    (caps : Tuple m.Val source.captures) (known : test f caps) : Known guard f := by
  subst source
  exact .callable i f caps (reads.symm ▸ known)

theorem oldKnown {left : Guard m earlier} (right : Guard m later)
    {ty : Ty V S} {value : m.Val ty} : Known left value → Known (left.combine right) value
  | .ordinary value plain => .ordinary value plain
  | .callable i f caps known =>
    atSlot (leftIndex earlier later i) (append_at_old earlier later i).symm (left i)
      (Guard.combine_left left right i) f caps known

theorem newKnown (left : Guard m earlier) {right : Guard m later}
    {ty : Ty V S} {value : m.Val ty} : Known right value → Known (left.combine right) value
  | .ordinary value plain => .ordinary value plain
  | .callable i f caps known =>
    atSlot (rightIndex earlier later i) (append_at_new earlier later i).symm (right i)
      (Guard.combine_right left right i) f caps known

theorem link_step (binding : GroupBinding Op later imports past calls familyPast)
    (actions : Actions m σ) (unitId : Nat) (inputs : Tuple m.Val imports)
    (locals : Locals m.Val past) (rest : ModuleTerm Op imports (past ++ [memberPorts later.members]) sigs exports)
    (store : σ) :
    Isomorphism.RecursiveCall.Numbered.Prefix.linkTerm actions unitId inputs locals (.bind (.phi binding.term) rest) store =
      Isomorphism.RecursiveCall.Numbered.Prefix.linkTerm actions unitId inputs (binding.locals inputs locals) rest store := by
  rw [Isomorphism.RecursiveCall.Numbered.Prefix.linkTerm_bind]
  rfl

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Groups.Proofs
