module

public import Silmaril.Formats.Dasl.Named.Lift.Defs
public import Silmaril.Formats.Dasl.Named.Thms
public import Silmaril.Formats.Dasl.Encode.Defs
import Silmaril.Proofs.Formats.Dasl.Named.Lift

public section

namespace Silmaril.Formats.Dasl

variable {Name Input : Type} {store choices : Store Name} {value : Value} {shallow : Shallow Name}

theorem CanName.mono {extended : Store Name} (names : CanName store value shallow)
    (incl : store.Subset extended) : CanName extended value shallow :=
  let ⟨tree, erased, view, admitted⟩ := canName_iff_exists_admitted.mp names
  canName_iff_exists_admitted.mpr ⟨tree, erased, view,
    ⟨fun _ _ hit => incl.1 (admitted.1 hit), fun _ _ hit => incl.2 (admitted.2 hit)⟩⟩

/-- The exact criterion keeps selection and store availability separate on the
same lift. It does not require binding of either relation. -/
theorem canName_selected_iff : CanName (store.selectedBy choices) value shallow ↔
    ∃ tree : Named Name, tree.erase = value ∧ tree.embed.shallow = shallow ∧
      tree.AdmittedBy choices ∧ tree.AdmittedBy store :=
  Proofs.Formats.Dasl.can_name_selected_iff

theorem Value.NamingCoverage.exists_canName (coverage : value.NamingCoverage store) :
    ∃ shallow, CanName store value shallow :=
  Proofs.Formats.Dasl.exists_can_name_of_coverage coverage

/-- Binding turns availability into compatibility; it does not provide names. -/
theorem CanName.lift_selected (names : CanName (store.selectedBy choices) value shallow)
    (bound : store.Binding) : ∃ tree : Named Name, tree.erase = value ∧ tree.embed.shallow = shallow ∧
      tree.AdmittedBy choices ∧ tree.Compatible store :=
  let ⟨tree, erased, view, selected, admitted⟩ := canName_selected_iff.mp names
  ⟨tree, erased, view, selected, bound, admitted⟩

theorem Value.NamingCoverage.lift_selected (coverage : value.NamingCoverage (store.selectedBy choices))
    (bound : store.Binding) : ∃ tree : Named Name, tree.erase = value ∧
      tree.AdmittedBy choices ∧ tree.Compatible store :=
  let ⟨_, names⟩ := coverage.exists_canName
  let ⟨tree, erased, _, selected, valid⟩ := names.lift_selected bound
  ⟨tree, erased, selected, valid⟩

/-- Applies to any successful encoder targeting abstract DASL. The decoder sees
the unchanged encoded value after erasure; this does not assert wire validity. -/
theorem Encode.PartialCodec.lift_named (codec : Encode.PartialCodec Input Value) {input : Input}
    (encoded : codec.encode? input = some value) (names : CanName (store.selectedBy choices) value shallow)
    (bound : store.Binding) : ∃ tree : Named Name, tree.erase = value ∧ tree.embed.shallow = shallow ∧
      tree.AdmittedBy choices ∧ tree.Compatible store ∧ codec.decode? tree.erase = some input :=
  let ⟨tree, erased, view, selected, valid⟩ := names.lift_selected bound
  ⟨tree, erased, view, selected, valid, erased.symm ▸ codec.recovers encoded⟩

theorem Encode.TotalCodec.lift_named (codec : Encode.TotalCodec Input Value) (input : Input)
    (names : CanName (store.selectedBy choices) (codec.encode input) shallow) (bound : store.Binding) :
    ∃ tree : Named Name, tree.erase = codec.encode input ∧ tree.embed.shallow = shallow ∧
      tree.AdmittedBy choices ∧ tree.Compatible store ∧ codec.decode? tree.erase = some input :=
  codec.partial.lift_named rfl names bound

theorem Encode.TotalCodec.lift_named_of_coverage (codec : Encode.TotalCodec Input Value) (input : Input)
    (coverage : (codec.encode input).NamingCoverage (store.selectedBy choices)) (bound : store.Binding) :
    ∃ tree : Named Name, tree.erase = codec.encode input ∧ tree.AdmittedBy choices ∧
      tree.Compatible store ∧ codec.decode? tree.erase = some input :=
  let ⟨_, names⟩ := coverage.exists_canName
  let ⟨tree, erased, _, selected, valid, recovered⟩ := codec.lift_named input names bound
  ⟨tree, erased, selected, valid, recovered⟩

end Silmaril.Formats.Dasl
