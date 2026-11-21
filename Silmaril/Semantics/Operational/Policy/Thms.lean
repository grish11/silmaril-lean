module

public import Silmaril.Semantics.Operational.Policy.Defs
import Silmaril.Proofs.Semantics.Operational.Policy.Simulation
import Silmaril.Proofs.Semantics.Operational.Policy.Transport
import Silmaril.Proofs.Semantics.Operational.Policy.Order

public section

namespace Silmaril.Semantics.Operational

universe u v w x
variable {S : Type u} {T : Type w} {U : Type x} {Obs : Type v}

open Silmaril.Proofs.Semantics.Operational.Policy in
theorem OpSem.Sound.may {candidate reference : OpSem S Obs} (sound : candidate.Sound reference)
    {start : S} {outcome : Outcome Obs} : candidate.May start outcome → reference.May start outcome :=
  sound_may sound

theorem OpSem.Normal.not_diverges {sem : OpSem S Obs} {source : S} (normal : sem.Normal source) :
    ¬ sem.Diverges source := fun infinite =>
  let ⟨target, edge, _⟩ := InfiniteTrace.unfold infinite
  normal target edge

namespace OpSim

variable {left : WithUB S Obs} {right : WithUB T Obs} {rel : S → T → Prop}
  {source next : S} {matched : T} {outcome : Outcome Obs}

open Silmaril.Proofs.Semantics.Operational.Policy

theorem reach (sim : OpSim left right rel) (related : rel source matched)
    (path : left.toOpSem.Reach source next) :
    ∃ target, right.toOpSem.Reach matched target ∧ rel next target := sim_reach sim related path

theorem may (sim : OpSim left right rel) (related : rel source matched) :
    left.toOpSem.May source outcome → right.toOpSem.May matched outcome := sim_may sim related

theorem ubReachable (sim : OpSim left right rel) (related : rel source matched) :
    left.UBReachable source → right.UBReachable matched := sim_ub sim related

theorem safe_of_safe (sim : OpSim left right rel) (related : rel source matched)
    (safe : right.SafeAt matched) : left.SafeAt source := fun bad => safe (sim.ubReachable related bad)

theorem id (sem : WithUB S Obs) : OpSim sem sem Eq := sim_id sem

theorem trans {last : WithUB U Obs} {second : T → U → Prop}
    (one : OpSim left right rel) (two : OpSim right last second) :
    OpSim left last (RelComp rel second) := sim_trans one two

end OpSim

@[simp] theorem relComp_eq_left (rel : S → T → Prop) : RelComp Eq rel = rel := by
  funext source target
  exact propext ⟨fun ⟨_, rfl, related⟩ => related, fun related => ⟨source, rfl, related⟩⟩

@[simp] theorem relComp_eq_right (rel : S → T → Prop) : RelComp rel Eq = rel := by
  funext source target
  exact propext ⟨fun ⟨_, related, rfl⟩ => related, fun related => ⟨target, related, rfl⟩⟩

theorem relComp_assoc {V : Type*} (first : S → T → Prop) (second : T → U → Prop) (third : U → V → Prop) :
    RelComp (RelComp first second) third = RelComp first (RelComp second third) := by
  funext source target
  exact propext ⟨fun ⟨last, ⟨middle, left, right⟩, edge⟩ => ⟨middle, left, last, right, edge⟩,
    fun ⟨middle, left, last, right, edge⟩ => ⟨last, ⟨middle, left, right⟩, edge⟩⟩

namespace WithUB

open Silmaril.Proofs.Semantics.Operational.Policy

variable {sem left right other : WithUB S Obs} {map : S → T} {good : S → Prop}
  {start : S} {outcome : Outcome Obs}

theorem ofOpSem_safe (ordinary : OpSem S Obs) (start : S) : (ofOpSem ordinary).SafeAt start :=
  fun ⟨_, _, bad⟩ => bad

theorem SafeAt.of_reach {target : S} (safe : sem.SafeAt start) (path : sem.toOpSem.Reach start target) :
    sem.SafeAt target := safe_of_reach safe path

theorem AgreeWhenSafe.may_iff (agree : left.AgreeWhenSafe right)
    (safeLeft : left.SafeAt start) (safeRight : right.SafeAt start) :
    left.toOpSem.May start outcome ↔ right.toOpSem.May start outcome := may_iff_when_safe agree safeLeft safeRight

theorem enforce_sound (sem : WithUB S Obs) (good : S → Prop) :
    (sem.enforce good).toOpSem.Sound sem.toOpSem :=
  Silmaril.Proofs.Semantics.Operational.Policy.enforce_sound sem good

theorem enforce_safe_iff : (sem.enforce good).SafeAt start ↔
    sem.SafeAt start ∧ ∀ ⦃target⦄, sem.toOpSem.Reach start target → good target :=
  Silmaril.Proofs.Semantics.Operational.Policy.enforce_safe_iff

theorem enforce_may_iff (accepts : ∀ ⦃target⦄, sem.toOpSem.Reach start target → good target) :
    (sem.enforce good).toOpSem.May start outcome ↔ sem.toOpSem.May start outcome :=
  Silmaril.Proofs.Semantics.Operational.Policy.enforce_may_iff accepts

theorem push_sim (sem : WithUB S Obs) (map : S → T) :
    OpSim sem (sem.push map) (fun s t => map s = t) := push_forward sem map

theorem Compatible.push_readback (valid : sem.Compatible map) :
    OpSim (sem.push map) sem (fun t s => map s = t) := push_backward valid

theorem Compatible.of_injective (injective : Function.Injective map) : sem.Compatible map :=
  injective_compatible injective

theorem Compatible.push_may_iff (valid : sem.Compatible map) :
    (sem.push map).toOpSem.May (map start) outcome ↔ sem.toOpSem.May start outcome :=
  ⟨valid.push_readback.may rfl, (sem.push_sim map).may rfl⟩

theorem Compatible.push_safe_iff (valid : sem.Compatible map) :
    (sem.push map).SafeAt (map start) ↔ sem.SafeAt start :=
  ⟨(sem.push_sim map).safe_of_safe rfl, valid.push_readback.safe_of_safe rfl⟩

theorem Compatible.push_diverges_iff (valid : sem.Compatible map) :
    (sem.push map).toOpSem.Diverges (map start) ↔ sem.toOpSem.Diverges start :=
  Silmaril.Proofs.Semantics.Operational.Policy.push_diverges_iff valid start

theorem quotient_may_iff (setoid : Setoid S) (valid : sem.Compatible (Quotient.mk setoid)) :
    (sem.quotient setoid).toOpSem.May (Quotient.mk setoid start) outcome ↔ sem.toOpSem.May start outcome :=
  valid.push_may_iff

theorem quotient_safe_iff (setoid : Setoid S) (valid : sem.Compatible (Quotient.mk setoid)) :
    (sem.quotient setoid).SafeAt (Quotient.mk setoid start) ↔ sem.SafeAt start :=
  valid.push_safe_iff

theorem lift_sim (sem : WithUB S Obs) (map : S → T) :
    OpSim sem (sem.lift map) (fun s t => map s = t) := lift_forward sem map

theorem Compatible.lift_readback (valid : sem.Compatible map) :
    OpSim (sem.lift map) sem (fun t s => map s = t) := lift_backward valid

theorem lift_may_iff (injective : Function.Injective map) :
    (sem.lift map).toOpSem.May (map start) outcome ↔ sem.toOpSem.May start outcome :=
  (Compatible.of_injective injective : sem.Compatible map).push_may_iff

theorem lift_step_iff (injective : Function.Injective map) (source target : S) :
    (sem.lift map).step (map source) (map target) ↔ sem.step source target :=
  Silmaril.Proofs.Semantics.Operational.Policy.lift_step_iff injective source target

theorem lift_observe_iff (injective : Function.Injective map) (source : S) (outcome : Outcome Obs) :
    (sem.lift map).observe (map source) outcome ↔ sem.observe source outcome :=
  Silmaril.Proofs.Semantics.Operational.Policy.lift_observe_iff injective source outcome

theorem lift_safe_iff (injective : Function.Injective map) :
    (sem.lift map).SafeAt (map start) ↔ sem.SafeAt start :=
  ⟨(sem.lift_sim map).safe_of_safe rfl,
    (Compatible.of_injective injective : sem.Compatible map).lift_readback.safe_of_safe rfl⟩

theorem lift_outside {source : T} (outside : ¬ ∃ left, map left = source) :
    (sem.lift map).ub source ∧ (sem.lift map).toOpSem.Normal source ∧
      ∀ outcome, ¬ (sem.lift map).toOpSem.May source outcome :=
  Silmaril.Proofs.Semantics.Operational.Policy.lift_outside outside

theorem restrict_sim (sem : WithUB S Obs) (good : S → Prop) :
    OpSim (sem.restrict good) sem (fun s t => s.val = t) := restrict_forward sem good

theorem restrict_readback (closed : ∀ ⦃source target⦄, good source → sem.step source target → good target) :
    OpSim sem (sem.restrict good) (fun s t => t.val = s) := restrict_backward closed

theorem restrict_may_iff (closed : ∀ ⦃source target⦄, good source → sem.step source target → good target)
    (source : Subtype good) :
    (sem.restrict good).toOpSem.May source outcome ↔ sem.toOpSem.May source.val outcome :=
  ⟨(sem.restrict_sim good).may rfl, (sem.restrict_readback closed).may rfl⟩

theorem restrict_lift_may_iff (closed : ∀ ⦃source target⦄, good source → sem.step source target → good target)
    (source : Subtype good) :
    ((sem.restrict good).lift Subtype.val).toOpSem.May source.val outcome ↔ sem.toOpSem.May source.val outcome :=
  (lift_may_iff Subtype.val_injective).trans (restrict_may_iff closed source)

theorem Included.refl (sem : WithUB S Obs) : sem.Included sem := included_refl sem

theorem Included.trans (first : left.Included right) (second : right.Included other) : left.Included other :=
  included_trans first second

theorem Included.antisymm (first : left.Included right) (second : right.Included left) : left = right :=
  included_antisymm first second

theorem included_meet : other.Included (left.meet right) ↔ other.Included left ∧ other.Included right :=
  Silmaril.Proofs.Semantics.Operational.Policy.included_meet

theorem join_included : (left.join right).Included other ↔ left.Included other ∧ right.Included other :=
  Silmaril.Proofs.Semantics.Operational.Policy.join_included

theorem SafeRefines.refl (sem : WithUB S Obs) : sem.SafeRefines sem :=
  fun {_} safe => ⟨safe, fun {_} obs => obs⟩

theorem SafeRefines.trans (first : left.SafeRefines right) (second : right.SafeRefines other) :
    left.SafeRefines other := fun {_} safe =>
  ⟨(first (second safe).1).1, fun {_} obs => (second safe).2 ((first (second safe).1).2 obs)⟩

end WithUB

end Silmaril.Semantics.Operational
