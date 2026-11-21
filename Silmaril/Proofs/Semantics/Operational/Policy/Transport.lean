module

public import Silmaril.Semantics.Operational.Policy.Defs

public section

namespace Silmaril.Proofs.Semantics.Operational.Policy

open Silmaril.Semantics.Operational

universe u v w
variable {S : Type u} {T : Type w} {Obs : Type v} {sem : WithUB S Obs} {map : S → T}

theorem push_forward (sem : WithUB S Obs) (map : S → T) :
    OpSim sem (sem.push map) (fun s t => map s = t) where
  step := by rintro source _ next rfl step; exact ⟨map next, .single ⟨source, next, rfl, rfl, step⟩, rfl⟩
  observe := by rintro source _ _ rfl obs; exact ⟨map source, .refl, source, rfl, obs⟩
  ub := by rintro source _ rfl bad; exact ⟨map source, .refl, source, rfl, bad⟩

theorem push_backward (valid : sem.Compatible map) :
    OpSim (sem.push map) sem (fun t s => map s = t) where
  step := by
    rintro _ source _ rfl ⟨representative, target, equal, rfl, step⟩
    obtain ⟨next, edge, eq⟩ := valid.step equal step
    exact ⟨next, .single edge, eq⟩
  observe := by
    rintro _ source _ rfl ⟨_, equal, obs⟩
    exact ⟨source, .refl, valid.observe equal obs⟩
  ub := by
    rintro _ source rfl ⟨_, equal, bad⟩
    exact ⟨source, .refl, valid.ub equal bad⟩

theorem injective_compatible (injective : Function.Injective map) : sem.Compatible map where
  step := by intro _ _ _ equal edge; exact ⟨_, injective equal ▸ edge, rfl⟩
  observe := by intro _ _ _ equal obs; exact injective equal ▸ obs
  ub := by intro _ _ equal bad; exact injective equal ▸ bad

theorem push_diverges_iff (valid : sem.Compatible map) (source : S) :
    (sem.push map).toOpSem.Diverges (map source) ↔ sem.toOpSem.Diverges source := by
  constructor
  · intro infinite
    refine InfiniteTrace.of_map map (fun _ => True) ?_ trivial infinite
    rintro _ _ _ ⟨other, target, equal, rfl, edge⟩
    obtain ⟨next, reflects, same⟩ := valid.step equal edge
    exact ⟨next, reflects, trivial, same⟩
  · intro infinite
    exact InfiniteTrace.map map (fun left right edge => ⟨left, right, rfl, rfl, edge⟩) infinite

theorem lift_step_iff (injective : Function.Injective map) (source target : S) :
    (sem.lift map).step (map source) (map target) ↔ sem.step source target := by
  constructor
  · rintro ⟨left, right, equalLeft, equalRight, edge⟩
    exact injective equalLeft ▸ injective equalRight ▸ edge
  · intro edge
    exact ⟨source, target, rfl, rfl, edge⟩

theorem lift_observe_iff (injective : Function.Injective map) (source : S) (outcome : Outcome Obs) :
    (sem.lift map).observe (map source) outcome ↔ sem.observe source outcome := by
  constructor
  · rintro ⟨left, equal, observed⟩
    exact injective equal ▸ observed
  · intro observed
    exact ⟨source, rfl, observed⟩

theorem lift_forward (sem : WithUB S Obs) (map : S → T) :
    OpSim sem (sem.lift map) (fun s t => map s = t) where
  step := (push_forward sem map).step
  observe := (push_forward sem map).observe
  ub := by rintro source _ rfl bad; exact ⟨map source, .refl, .inl ⟨source, rfl, bad⟩⟩

theorem lift_backward (valid : sem.Compatible map) :
    OpSim (sem.lift map) sem (fun t s => map s = t) where
  step := (push_backward valid).step
  observe := (push_backward valid).observe
  ub := by
    rintro _ source rfl (bad | outside)
    · exact (push_backward valid).ub (show map source = map source from rfl) bad
    · exact (outside ⟨source, rfl⟩).elim

theorem lift_outside {source : T} (outside : ¬ ∃ left, map left = source) :
    (sem.lift map).ub source ∧ (sem.lift map).toOpSem.Normal source ∧
      ∀ outcome, ¬ (sem.lift map).toOpSem.May source outcome := by
  have normal : (sem.lift map).toOpSem.Normal source := by
    rintro _ ⟨left, _, equal, _, _⟩
    exact outside ⟨left, equal⟩
  have pathEq : ∀ {target}, (sem.lift map).toOpSem.Reach source target → target = source := by
    intro target path
    induction path with
    | refl => rfl
    | tail _ step ih => cases ih; exact (normal _ step).elim
  refine ⟨.inr outside, normal, ?_⟩
  rintro outcome ⟨target, path, observed⟩
  have observedSource : (sem.lift map).observe source outcome := pathEq path ▸ observed
  obtain ⟨left, equal, _⟩ := observedSource
  exact outside ⟨left, equal⟩

theorem restrict_forward (sem : WithUB S Obs) (good : S → Prop) :
    OpSim (sem.restrict good) sem (fun s t => s.val = t) where
  step := by rintro _ _ next rfl edge; exact ⟨next.val, .single edge, rfl⟩
  observe := by rintro source _ _ rfl obs; exact ⟨source.val, .refl, obs⟩
  ub := by rintro source _ rfl bad; exact ⟨source.val, .refl, bad⟩

theorem restrict_backward {good : S → Prop}
    (closed : ∀ ⦃source target⦄, good source → sem.step source target → good target) :
    OpSim sem (sem.restrict good) (fun s t => t.val = s) where
  step := by
    rintro _ source next rfl edge
    exact ⟨⟨next, closed source.property edge⟩, .single edge, rfl⟩
  observe := by rintro _ source _ rfl obs; exact ⟨source, .refl, obs⟩
  ub := by rintro _ source rfl bad; exact ⟨source, .refl, bad⟩

end Silmaril.Proofs.Semantics.Operational.Policy
