module

public import Silmaril.Formats.Dasl.Named.Defs
public import Silmaril.Formats.Dasl.Resolve.Thms
import Silmaril.Proofs.Formats.Dasl.Named

public section

namespace Silmaril.Formats.Dasl

variable {Name : Type} {store : Store Name} {tree : Named Name}

theorem Named.admitted_observed (tree : Named Name) : tree.AdmittedBy tree.observed :=
  ⟨fun _ _ hit => hit, fun _ _ hit => hit⟩

theorem Named.Compatible.coherent (valid : tree.Compatible store) : tree.Coherent :=
  valid.1.subset valid.2

theorem Named.coherent_iff_exists_compatible : tree.Coherent ↔ ∃ store, tree.Compatible store :=
  ⟨fun bound => ⟨tree.observed, bound, tree.admitted_observed⟩, fun ⟨_, valid⟩ => valid.coherent⟩

theorem Named.coherent_iff_no_conflict : tree.Coherent ↔ ¬tree.Conflict :=
  Proofs.Formats.Dasl.coherent_iff_no_conflict tree

theorem Named.Conflict.not_compatible (conflict : tree.Conflict) : ¬tree.Compatible store :=
  fun valid => Named.coherent_iff_no_conflict.mp valid.coherent conflict

theorem Named.admitted_iff_expands : tree.AdmittedBy store ↔ Expands store tree.embed.shallow tree :=
  ⟨Proofs.Formats.Dasl.expands_of_admitted, Expands.bindings_subset⟩

theorem canName_iff_exists_admitted {value : Value} {source : Shallow Name} :
    CanName store value source ↔
      ∃ tree : Named Name, tree.erase = value ∧ tree.embed.shallow = source ∧ tree.AdmittedBy store :=
  ⟨fun choices => let ⟨tree, eq, expanded⟩ := Proofs.Formats.Dasl.can_name_lift choices
    ⟨tree, eq, expanded.shallow_eq, expanded.bindings_subset⟩,
   fun ⟨_, erased, shallow, admitted⟩ => erased ▸ shallow ▸
      Proofs.Formats.Dasl.can_name_of_expands (Named.admitted_iff_expands.mp admitted)⟩

theorem exists_compatible_lift_iff {value : Value} :
    (∃ tree : Named Name, tree.erase = value ∧ tree.Compatible store) ↔
      store.Binding ∧ ∃ source, CanName store value source :=
  ⟨fun ⟨_, eq, bound, admitted⟩ => ⟨bound, _, canName_iff_exists_admitted.mpr ⟨_, eq, rfl, admitted⟩⟩,
   fun ⟨bound, _, choices⟩ => let ⟨tree, eq, _, admitted⟩ := canName_iff_exists_admitted.mp choices
     ⟨tree, eq, bound, admitted⟩⟩

end Silmaril.Formats.Dasl
