module

public import Silmaril.Formats.Dasl.Named.Lift.Defs
public import Silmaril.Formats.Dasl.Named.Thms

public section

namespace Silmaril.Proofs.Formats.Dasl

open Silmaril.Formats.Dasl

variable {Name : Type} {store choices : Store Name} {value : Value} {shallow : Shallow Name}

theorem can_name_selected_iff : CanName (store.selectedBy choices) value shallow ↔
    ∃ tree : Named Name, tree.erase = value ∧ tree.embed.shallow = shallow ∧
      tree.AdmittedBy choices ∧ tree.AdmittedBy store := by
  rw [canName_iff_exists_admitted]
  constructor
  · rintro ⟨tree, erased, view, admitted⟩
    exact ⟨tree, erased, view, ⟨fun _ _ hit => (admitted.1 hit).1, fun _ _ hit => (admitted.2 hit).1⟩,
      ⟨fun _ _ hit => (admitted.1 hit).2, fun _ _ hit => (admitted.2 hit).2⟩⟩
  · rintro ⟨tree, erased, view, selected, admitted⟩
    exact ⟨tree, erased, view, ⟨fun _ _ hit => ⟨selected.1 hit, admitted.1 hit⟩,
      fun _ _ hit => ⟨selected.2 hit, admitted.2 hit⟩⟩⟩

theorem exists_can_name_of_coverage (coverage : value.NamingCoverage store) :
    ∃ shallow, CanName store value shallow := by
  classical
  induction value with
  | ref impossible => exact impossible.elim
  | obj unnamed child ih =>
    cases unnamed
    obtain ⟨childCovered, available⟩ := coverage
    obtain ⟨shallow, named⟩ := ih childCovered
    obtain ⟨name, hit⟩ := available named
    exact ⟨.ref (.obj name), .obj named hit⟩
  | blob unnamed bytes =>
    cases unnamed
    obtain ⟨name, hit⟩ := coverage
    exact ⟨.ref (.blob name), .blob hit⟩
  | dict keys children ih =>
    choose views named using fun key => ih key (coverage key)
    exact ⟨.dict keys views, .dict named⟩
  | list len children ih =>
    choose views named using fun index => ih index (coverage index)
    exact ⟨.list len views, .list named⟩
  | _ => exact ⟨_, by constructor⟩

end Silmaril.Proofs.Formats.Dasl
