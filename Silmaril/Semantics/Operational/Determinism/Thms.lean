module

public import Silmaril.Semantics.Operational.Determinism.Defs
public import Silmaril.Semantics.Operational.Policy.Thms
import Silmaril.Proofs.Semantics.Operational.Determinism.Policy

public section

namespace Silmaril.Semantics.Operational

variable {S O K : Type*}

namespace OpSem

theorem resultDetAt_iff {sem : OpSem S O} {start : S} :
    sem.ResultDetAt start ↔ ∀ ⦃left right⦄, sem.May start left → sem.May start right → left = right :=
  Proofs.Semantics.Operational.Determinism.resultDetAt_iff

theorem nonTrapDetAt_iff {sem : OpSem S O} {start : S} :
    sem.NonTrapDetAt start ↔
      ∀ ⦃left right⦄, sem.May start (.returned left) → sem.May start (.returned right) → left = right :=
  Proofs.Semantics.Operational.Determinism.nonTrapDetAt_iff

theorem ViewDetAt.of_reach {sem : OpSem S O} {view : Outcome O → Option K} {start target : S}
    (det : sem.ViewDetAt view start) (path : sem.Reach start target) : sem.ViewDetAt view target :=
  Proofs.Semantics.Operational.Determinism.viewDetAt_of_reach det path

theorem prefix_good_iff {sem : OpSem S O} {good : S → Prop} {start : S} :
    sem.PrefixGood (sem.PrefixGood good) start ↔ sem.PrefixGood good start :=
  Proofs.Semantics.Operational.Determinism.prefix_good_iff

end OpSem

namespace WithUB

variable {sem : WithUB S O} {start : S} {good : S → Prop}

theorem enforce_ubReachable_iff (sem : WithUB S O) (good : S → Prop) (start : S) :
    (sem.enforce good).UBReachable start ↔ sem.UBReachable start ∨
      ∃ target, sem.toOpSem.Reach start target ∧ ¬ good target :=
  Proofs.Semantics.Operational.Determinism.enforce_ubReachable_iff sem good start

theorem requireLocalDet_safe_iff :
    sem.requireLocalDet.SafeAt start ↔ sem.SafeAt start ∧ sem.toOpSem.DetFrom start :=
  enforce_safe_iff

theorem requirePrefix_safe_iff :
    (sem.requirePrefix good).SafeAt start ↔ (sem.enforce good).SafeAt start :=
  enforce_safe_iff.trans ((and_congr_right fun _ => OpSem.prefix_good_iff).trans enforce_safe_iff.symm)

theorem requireViewDet_safe_iff {view : Outcome O → Option K} :
    (sem.requireViewDet view).SafeAt start ↔ sem.SafeAt start ∧ sem.toOpSem.ViewDetAt view start :=
  Proofs.Semantics.Operational.Determinism.requireViewDet_safe_iff

/-- When the added policy is safe, all original transitions and observations
at that source are recovered, not just the finite may-outcomes. -/
theorem enforce_complete_on_safe :
    sem.toOpSem.SoundOn (sem.enforce good).toOpSem (sem.enforce good).SafeAt :=
  fun {_} safe => let admits := (enforce_safe_iff.mp safe).2 .refl
    ⟨fun {_} step => ⟨admits, step⟩, fun {_} observe => ⟨admits, observe⟩⟩

theorem original_safeRefines_enforce (sem : WithUB S O) (good : S → Prop) : sem.SafeRefines (sem.enforce good) :=
  Proofs.Semantics.Operational.Determinism.original_safeRefines_enforce sem good

theorem enforce_safeRefines_iff (sem : WithUB S O) (good : S → Prop) :
    (sem.enforce good).SafeRefines sem ↔ ∀ ⦃start⦄, sem.SafeAt start → sem.toOpSem.PrefixGood good start :=
  Proofs.Semantics.Operational.Determinism.enforce_safeRefines_iff sem good

variable {left right other : WithUB S O}

theorem Permits.refl (sem : WithUB S O) : sem.Permits sem := ⟨⟨fun {_ _} => id, fun {_ _} => id⟩, fun {_} => id⟩

theorem Permits.trans (first : left.Permits right) (second : right.Permits other) : left.Permits other :=
  ⟨⟨fun {_ _} edge => first.1.1 (second.1.1 edge), fun {_ _} obs => first.1.2 (second.1.2 obs)⟩,
    fun {_} ub => second.2 (first.2 ub)⟩

theorem Permits.antisymm (first : left.Permits right) (second : right.Permits left) : left = right :=
  Included.antisymm ⟨second.1, first.2⟩ ⟨first.1, second.2⟩

theorem permits_join : other.Permits (left.permitJoin right) ↔ other.Permits left ∧ other.Permits right :=
  Proofs.Semantics.Operational.Determinism.permits_join

theorem meet_permits : (left.permitMeet right).Permits other ↔ left.Permits other ∧ right.Permits other :=
  Proofs.Semantics.Operational.Determinism.meet_permits

theorem enforce_permits {more less : S → Prop} (implies : ∀ ⦃s⦄, less s → more s) :
    (sem.enforce more).Permits (sem.enforce less) :=
  ⟨⟨fun {_ _} edge => ⟨implies edge.1, edge.2⟩, fun {_ _} obs => ⟨implies obs.1, obs.2⟩⟩,
    fun {_} ub => ub.imp_right fun bad good => bad (implies good)⟩

end WithUB
end Silmaril.Semantics.Operational
