module

public import Silmaril.Semantics.Operational.Determinism.Defs
public import Silmaril.Semantics.Operational.Policy.Thms

public section

namespace Silmaril.Proofs.Semantics.Operational.Determinism

open Silmaril.Semantics.Operational

variable {S O K : Type*}

theorem resultDetAt_iff {sem : OpSem S O} {start : S} :
    sem.ResultDetAt start ↔ ∀ ⦃left right⦄, sem.May start left → sem.May start right → left = right := by
  constructor
  · intro det left right hasLeft hasRight
    exact det hasLeft hasRight rfl rfl
  · intro det left right key₁ key₂ hasLeft hasRight projectsLeft projectsRight
    cases Option.some.inj projectsLeft
    cases Option.some.inj projectsRight
    exact det hasLeft hasRight

theorem nonTrapDetAt_iff {sem : OpSem S O} {start : S} :
    sem.NonTrapDetAt start ↔
      ∀ ⦃left right⦄, sem.May start (.returned left) → sem.May start (.returned right) → left = right := by
  constructor
  · intro det left right hasLeft hasRight
    exact det hasLeft hasRight rfl rfl
  · intro det left right key₁ key₂ hasLeft hasRight projectsLeft projectsRight
    cases left <;> cases right <;> cases projectsLeft <;> cases projectsRight
    exact det hasLeft hasRight

theorem viewDetAt_of_reach {sem : OpSem S O} {view : Outcome O → Option K} {start target : S}
    (det : sem.ViewDetAt view start) (path : sem.Reach start target) : sem.ViewDetAt view target := by
  intro left right key₁ key₂ hasLeft hasRight projectsLeft projectsRight
  obtain ⟨lastLeft, leftPath, observedLeft⟩ := hasLeft
  obtain ⟨lastRight, rightPath, observedRight⟩ := hasRight
  exact det ⟨lastLeft, path.trans leftPath, observedLeft⟩ ⟨lastRight, path.trans rightPath, observedRight⟩
    projectsLeft projectsRight

theorem prefix_good_iff {sem : OpSem S O} {good : S → Prop} {start : S} :
    sem.PrefixGood (sem.PrefixGood good) start ↔ sem.PrefixGood good start := by
  exact ⟨fun all => all .refl, fun all _ path _ rest => all (path.trans rest)⟩

theorem enforce_ubReachable_iff (sem : WithUB S O) (good : S → Prop) (start : S) :
    (sem.enforce good).UBReachable start ↔ sem.UBReachable start ∨
      ∃ target, sem.toOpSem.Reach start target ∧ ¬ good target := by
  classical
  constructor
  · intro marked
    by_contra absent
    have absent := not_or.mp absent
    apply (WithUB.enforce_safe_iff.mpr ⟨absent.1, ?_⟩) marked
    intro target path
    by_contra bad
    exact absent.2 ⟨target, path, bad⟩
  · intro found
    by_contra safe
    obtain ⟨base, accepts⟩ := WithUB.enforce_safe_iff.mp safe
    rcases found with baseUB | ⟨target, path, bad⟩
    · exact base baseUB
    · exact bad (accepts path)

theorem requireViewDet_safe_iff {sem : WithUB S O} {view : Outcome O → Option K} {start : S} :
    (sem.requireViewDet view).SafeAt start ↔ sem.SafeAt start ∧ sem.toOpSem.ViewDetAt view start := by
  exact WithUB.enforce_safe_iff.trans
    ⟨fun ⟨safe, det⟩ => ⟨safe, det .refl⟩, fun ⟨safe, det⟩ => ⟨safe, fun {_} => viewDetAt_of_reach det⟩⟩

theorem original_safeRefines_enforce (sem : WithUB S O) (good : S → Prop) : sem.SafeRefines (sem.enforce good) := by
  intro start safe
  have original := WithUB.enforce_safe_iff.mp safe
  exact ⟨original.1, fun {_} may => (WithUB.enforce_may_iff original.2).mpr may⟩

theorem enforce_safeRefines_iff (sem : WithUB S O) (good : S → Prop) :
    (sem.enforce good).SafeRefines sem ↔ ∀ ⦃start⦄, sem.SafeAt start → sem.toOpSem.PrefixGood good start := by
  constructor
  · intro refines start safe
    exact (WithUB.enforce_safe_iff.mp (refines safe).1).2
  · intro accepts start safe
    exact ⟨WithUB.enforce_safe_iff.mpr ⟨safe, accepts safe⟩,
      fun {_} may => (WithUB.enforce_may_iff (accepts safe)).mp may⟩

variable {left right other : WithUB S O}

theorem permits_join : other.Permits (left.permitJoin right) ↔ other.Permits left ∧ other.Permits right :=
  ⟨fun allows => ⟨⟨⟨fun {_ _} edge => allows.1.1 (.inl edge), fun {_ _} obs => allows.1.2 (.inl obs)⟩,
      fun {_} ub => (allows.2 ub).1⟩, ⟨⟨fun {_ _} edge => allows.1.1 (.inr edge), fun {_ _} obs => allows.1.2 (.inr obs)⟩,
      fun {_} ub => (allows.2 ub).2⟩⟩,
   fun ⟨hl, hr⟩ => ⟨⟨fun {_ _} edge => edge.elim (fun h => hl.1.1 h) (fun h => hr.1.1 h),
     fun {_ _} obs => obs.elim (fun h => hl.1.2 h) (fun h => hr.1.2 h)⟩,
     fun {_} ub => ⟨hl.2 ub, hr.2 ub⟩⟩⟩

theorem meet_permits : (left.permitMeet right).Permits other ↔ left.Permits other ∧ right.Permits other :=
  ⟨fun allows => ⟨⟨⟨fun {_ _} edge => (allows.1.1 edge).1, fun {_ _} obs => (allows.1.2 obs).1⟩,
      fun {_} ub => allows.2 (.inl ub)⟩, ⟨⟨fun {_ _} edge => (allows.1.1 edge).2, fun {_ _} obs => (allows.1.2 obs).2⟩,
      fun {_} ub => allows.2 (.inr ub)⟩⟩,
   fun ⟨hl, hr⟩ => ⟨⟨fun {_ _} edge => ⟨hl.1.1 edge, hr.1.1 edge⟩, fun {_ _} obs => ⟨hl.1.2 obs, hr.1.2 obs⟩⟩,
      fun {_} ub => ub.elim (fun h => hl.2 h) (fun h => hr.2 h)⟩⟩

end Silmaril.Proofs.Semantics.Operational.Determinism
