module

public import Silmaril.Semantics.Operational.Program.Defs
import Silmaril.Semantics.Operational.Policy.Thms

public section

namespace Silmaril.Proofs.Semantics.Operational.Program

open Silmaril.Semantics.Operational

universe p q s t o v
variable {Program : Type p} {Other : Type q} {State : Type s} {Target : Type t}
  {Obs : Type o} {View : Type v} {model : HasOpSem Program State Obs}
  {program : Program} {outcome : Outcome Obs}

theorem safeFragment_may_iff : model.safeFragment.May program outcome ↔
    ∃ start, model.initial program start ∧ model.semantics.SafeAt start ∧ model.semantics.toOpSem.May start outcome := by
  have closed : ∀ ⦃source target⦄, model.semantics.SafeAt source → model.semantics.step source target →
      model.semantics.SafeAt target := fun {_ _} safe edge => safe.of_reach (.single edge)
  constructor
  · rintro ⟨start, init, may⟩
    exact ⟨start.val, init, start.property, (WithUB.restrict_may_iff closed start).mp may⟩
  · rintro ⟨start, init, safe, may⟩
    exact ⟨⟨start, safe⟩, init, (WithUB.restrict_may_iff closed ⟨start, safe⟩).mpr may⟩

theorem mapObservations_may_iff (view : Obs → View) (observed : Outcome View) :
    (model.mapObservations view).May program observed ↔
      ∃ original, model.May program original ∧ original.map view = observed := by
  constructor
  · rintro ⟨start, init, finish, path, original, recorded, mapped⟩
    exact ⟨original, ⟨start, init, finish, path, recorded⟩, mapped⟩
  · rintro ⟨original, ⟨start, init, finish, path, recorded⟩, mapped⟩
    exact ⟨start, init, finish, path, original, recorded, mapped⟩

theorem refines_of_sim {reference : HasOpSem Other Target Obs} {other : Other} {rel : State → Target → Prop}
    (sim : OpSim model.semantics reference.semantics rel)
    (entry : ∀ ⦃start⦄, model.initial program start → ∃ target, reference.initial other target ∧ rel start target) :
    model.Refines program reference other := by
  constructor
  · rintro ⟨start, init, ub⟩
    obtain ⟨target, init', related⟩ := entry init
    exact ⟨target, init', sim.ubReachable related ub⟩
  · rintro seen ⟨start, init, may⟩
    obtain ⟨target, init', related⟩ := entry init
    exact ⟨target, init', sim.may related may⟩

end Silmaril.Proofs.Semantics.Operational.Program
