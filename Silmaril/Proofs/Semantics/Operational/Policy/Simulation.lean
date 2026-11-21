module

public import Silmaril.Semantics.Operational.Policy.Defs

public section

namespace Silmaril.Proofs.Semantics.Operational.Policy

open Silmaril.Semantics.Operational

universe u v w x

variable {S : Type u} {T : Type w} {U : Type x} {Obs : Type v}

theorem sound_may {candidate reference : OpSem S Obs} (sound : candidate.Sound reference)
    {start : S} {outcome : Outcome Obs} (seen : candidate.May start outcome) :
    reference.May start outcome := by
  obtain ⟨target, path, observation⟩ := seen
  exact ⟨target, Relation.ReflTransGen.mono (fun _ _ step => sound.1 step) _ _ path, sound.2 observation⟩

theorem safe_of_reach {sem : WithUB S Obs} {source target : S} (safe : sem.SafeAt source)
    (path : sem.toOpSem.Reach source target) : sem.SafeAt target := by
  rintro ⟨last, tail, bad⟩
  exact safe ⟨last, path.trans tail, bad⟩

theorem may_when_safe {left right : WithUB S Obs} {start : S} {outcome : Outcome Obs}
    (sound : left.toOpSem.SoundOn right.toOpSem (fun s => left.SafeAt s ∧ right.SafeAt s))
    (safeLeft : left.SafeAt start) (safeRight : right.SafeAt start)
    (seen : left.toOpSem.May start outcome) : right.toOpSem.May start outcome := by
  have transfer : ∀ {target}, left.toOpSem.Reach start target → right.toOpSem.Reach start target := by
    intro target path
    induction path with
    | refl => exact .refl
    | tail earlier step ih =>
      exact ih.tail ((sound ⟨safe_of_reach safeLeft earlier, safe_of_reach safeRight ih⟩).1 step)
  obtain ⟨target, path, observed⟩ := seen
  exact ⟨target, transfer path,
    (sound ⟨safe_of_reach safeLeft path, safe_of_reach safeRight (transfer path)⟩).2 observed⟩

theorem may_iff_when_safe {left right : WithUB S Obs} {start : S} {outcome : Outcome Obs}
    (agree : left.AgreeWhenSafe right) (safeLeft : left.SafeAt start) (safeRight : right.SafeAt start) :
    left.toOpSem.May start outcome ↔ right.toOpSem.May start outcome :=
  ⟨may_when_safe agree.1 safeLeft safeRight,
    may_when_safe (fun {_} safe => agree.2 ⟨safe.2, safe.1⟩) safeRight safeLeft⟩

theorem sim_reach {left : WithUB S Obs} {right : WithUB T Obs} {rel : S → T → Prop}
    (sim : OpSim left right rel) {source next : S} {matched : T}
    (related : rel source matched) (path : left.toOpSem.Reach source next) :
    ∃ target, right.toOpSem.Reach matched target ∧ rel next target := by
  induction path with
  | refl => exact ⟨matched, .refl, related⟩
  | tail _ step ih =>
    obtain ⟨middle, earlier, relMiddle⟩ := ih
    obtain ⟨target, tail, relTarget⟩ := sim.step relMiddle step
    exact ⟨target, earlier.trans tail, relTarget⟩

theorem sim_may {left : WithUB S Obs} {right : WithUB T Obs} {rel : S → T → Prop}
    (sim : OpSim left right rel) {source : S} {matched : T} {outcome : Outcome Obs}
    (related : rel source matched) (seen : left.toOpSem.May source outcome) :
    right.toOpSem.May matched outcome := by
  obtain ⟨next, path, observe⟩ := seen
  obtain ⟨middle, earlier, relMiddle⟩ := sim_reach sim related path
  obtain ⟨target, tail, observe⟩ := sim.observe relMiddle observe
  exact ⟨target, earlier.trans tail, observe⟩

theorem sim_ub {left : WithUB S Obs} {right : WithUB T Obs} {rel : S → T → Prop}
    (sim : OpSim left right rel) {source : S} {matched : T}
    (related : rel source matched) (bad : left.UBReachable source) : right.UBReachable matched := by
  obtain ⟨next, path, ub⟩ := bad
  obtain ⟨middle, earlier, relMiddle⟩ := sim_reach sim related path
  obtain ⟨target, tail, ub⟩ := sim.ub relMiddle ub
  exact ⟨target, earlier.trans tail, ub⟩

theorem sim_id (sem : WithUB S Obs) : OpSim sem sem Eq where
  step := by rintro _ _ next rfl step; exact ⟨next, .single step, rfl⟩
  observe := by rintro source _ _ rfl obs; exact ⟨source, .refl, obs⟩
  ub := by rintro source _ rfl bad; exact ⟨source, .refl, bad⟩

theorem sim_trans {left : WithUB S Obs} {middle : WithUB T Obs} {right : WithUB U Obs}
    {first : S → T → Prop} {second : T → U → Prop}
    (one : OpSim left middle first) (two : OpSim middle right second) :
    OpSim left right (RelComp first second) where
  step := by
    rintro _ _ _ ⟨matched, firstRel, secondRel⟩ step
    obtain ⟨middleNext, path, newFirst⟩ := one.step firstRel step
    obtain ⟨target, path, newSecond⟩ := sim_reach two secondRel path
    exact ⟨target, path, middleNext, newFirst, newSecond⟩
  observe := by
    rintro _ _ _ ⟨_, firstRel, secondRel⟩ observation
    exact sim_may two secondRel (one.observe firstRel observation)
  ub := by
    rintro _ _ ⟨_, firstRel, secondRel⟩ violation
    exact sim_ub two secondRel (one.ub firstRel violation)

theorem enforce_sound (sem : WithUB S Obs) (good : S → Prop) :
    (sem.enforce good).toOpSem.Sound sem.toOpSem :=
  ⟨fun {_ _} h => h.2, fun {_ _} h => h.2⟩

theorem enforce_safe_iff {sem : WithUB S Obs} {good : S → Prop} {start : S} :
    (sem.enforce good).SafeAt start ↔
      sem.SafeAt start ∧ ∀ ⦃target⦄, sem.toOpSem.Reach start target → good target := by
  classical
  constructor
  · intro safe
    have transfer : ∀ {target}, sem.toOpSem.Reach start target → (sem.enforce good).toOpSem.Reach start target := by
      intro target path
      induction path with
      | refl => exact .refl
      | tail _ step ih => exact ih.tail ⟨Classical.byContradiction
          (fun bad => safe ⟨_, ih, .inr bad⟩), step⟩
    exact ⟨by rintro ⟨target, path, bad⟩; exact safe ⟨target, transfer path, .inl bad⟩,
      fun {_} path => Classical.byContradiction fun bad => safe ⟨_, transfer path, .inr bad⟩⟩
  · rintro ⟨safe, accepts⟩ ⟨target, path, bad | outside⟩
    · exact safe ⟨target, Relation.ReflTransGen.mono (fun _ _ step => step.2) _ _ path, bad⟩
    · exact outside (accepts (Relation.ReflTransGen.mono (fun _ _ step => step.2) _ _ path))

theorem enforce_may_iff {sem : WithUB S Obs} {good : S → Prop} {start : S} {outcome : Outcome Obs}
    (accepts : ∀ ⦃target⦄, sem.toOpSem.Reach start target → good target) :
    (sem.enforce good).toOpSem.May start outcome ↔ sem.toOpSem.May start outcome := by
  refine ⟨sound_may (enforce_sound sem good), ?_⟩
  have transfer : ∀ {target}, sem.toOpSem.Reach start target → (sem.enforce good).toOpSem.Reach start target := by
    intro target path
    induction path with
    | refl => exact .refl
    | tail earlier edge ih => exact ih.tail ⟨accepts earlier, edge⟩
  rintro ⟨target, path, observe⟩
  exact ⟨target, transfer path, accepts path, observe⟩

end Silmaril.Proofs.Semantics.Operational.Policy
