module

public import Silmaril.Semantics.Operational.Program.Defs
public import Silmaril.Semantics.Operational.Policy.Thms
import Silmaril.Proofs.Semantics.Operational.Program

public section

namespace Silmaril.Semantics.Operational.HasOpSem

universe p q r s t u o v
variable {Program : Type p} {Other : Type q} {Third : Type r}
  {State : Type s} {Target : Type t} {Last : Type u} {Obs : Type o} {View : Type v}
  {model : HasOpSem Program State Obs} {reference : HasOpSem Other Target Obs} {last : HasOpSem Third Last Obs}
  {program : Program} {other : Other} {third : Third} {outcome : Outcome Obs}

theorem noEntry_not_may (missing : model.NoEntry program) : ¬ model.May program outcome :=
  fun ⟨start, init, _⟩ => missing ⟨start, init⟩

theorem noEntry_not_ub (missing : model.NoEntry program) : ¬ model.UBReachable program :=
  fun ⟨start, init, _⟩ => missing ⟨start, init⟩

theorem safeFragment_may_iff : model.safeFragment.May program outcome ↔
    ∃ start, model.initial program start ∧ model.semantics.SafeAt start ∧ model.semantics.toOpSem.May start outcome :=
  Proofs.Semantics.Operational.Program.safeFragment_may_iff

theorem safeFragment_noUB : ¬ model.safeFragment.UBReachable program :=
  fun ⟨_, _, target, _, ub⟩ => target.property ⟨target.val, .refl, ub⟩

theorem mapObservations_may_iff (view : Obs → View) (observed : Outcome View) :
    (model.mapObservations view).May program observed ↔
      ∃ original, model.May program original ∧ original.map view = observed :=
  Proofs.Semantics.Operational.Program.mapObservations_may_iff view observed

theorem mapObservations_precompose (erase : Other → Program) (view : Obs → View) :
    (model.precompose erase).mapObservations view = (model.mapObservations view).precompose erase := rfl

theorem Refines.mapObservations (refines : model.Refines program reference other) (view : Obs → View) :
    (model.mapObservations view).Refines program (reference.mapObservations view) other :=
  ⟨refines.1, fun observed may =>
    let ⟨original, seen, mapped⟩ := (mapObservations_may_iff view observed).mp may
    (mapObservations_may_iff view observed).mpr ⟨original, refines.2 seen, mapped⟩⟩

theorem UBRefines.refl : model.UBRefines program model program := id

theorem UBRefines.trans (first : model.UBRefines program reference other)
    (second : reference.UBRefines other last third) : model.UBRefines program last third := second ∘ first

theorem Refines.refl : model.Refines program model program := ⟨UBRefines.refl, fun _ seen => seen⟩

theorem Refines.trans (first : model.Refines program reference other) (second : reference.Refines other last third) :
    model.Refines program last third := ⟨first.1.trans second.1, fun _ seen => second.2 (first.2 seen)⟩

theorem Equivalent.refl : model.Equivalent program model program := ⟨Refines.refl, Refines.refl⟩

theorem Equivalent.symm (equiv : model.Equivalent program reference other) : reference.Equivalent other model program :=
  ⟨equiv.2, equiv.1⟩

theorem Equivalent.trans (first : model.Equivalent program reference other) (second : reference.Equivalent other last third) :
    model.Equivalent program last third := ⟨first.1.trans second.1, second.2.trans first.2⟩

theorem equivalent_iff : model.Equivalent program reference other ↔
    model.SameFinite program reference other ∧ (model.UBReachable program ↔ reference.UBReachable other) :=
  ⟨fun both => ⟨Set.Subset.antisymm both.1.2 both.2.2, ⟨both.1.1, both.2.1⟩⟩,
    fun ⟨same, ub⟩ => ⟨⟨ub.mp, same.subset⟩, ⟨ub.mpr, same.symm.subset⟩⟩⟩

theorem refines_of_sim {rel : State → Target → Prop} (sim : OpSim model.semantics reference.semantics rel)
    (entry : ∀ ⦃start⦄, model.initial program start → ∃ target, reference.initial other target ∧ rel start target) :
    model.Refines program reference other := Proofs.Semantics.Operational.Program.refines_of_sim sim entry

end Silmaril.Semantics.Operational.HasOpSem
