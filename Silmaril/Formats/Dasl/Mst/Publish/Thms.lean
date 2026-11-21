module

public import Silmaril.Formats.Dasl.Mst.Publish.Defs
import Silmaril.Proofs.Formats.Dasl.MstPublish

public section

namespace Silmaril.Formats.Dasl.Mst

open Silmaril.Semantics.Naming

variable {Name : Type}

theorem PublishProfile.graph_compatible {profile : PublishProfile Name} {layerOf : Key → Nat}
    {records : List (Record Name)} {built : Built Name} (hit : build layerOf profile.nameNode? records = some built) :
    Subset (profile.byteObservations built) (fun name bytes => profile.name? bytes = some name) :=
  Proofs.Formats.Dasl.MstPublish.graph_compatible hit

theorem PublishProfile.publish_spec [DecidableEq Name] {profile : PublishProfile Name} {layerOf : Key → Nat}
    {records : List (Record Name)} {built : Built Name} (hit : build layerOf profile.nameNode? records = some built)
    (read : Name → Option ByteArray) : profile.Spec layerOf records read built (profile.publish layerOf records read) :=
  Proofs.Formats.Dasl.MstPublish.publish_spec hit read

theorem PublishProfile.publish_accepts_iff [DecidableEq Name] {profile : PublishProfile Name} {layerOf : Key → Nat}
    {records : List (Record Name)} {built : Built Name} (hit : build layerOf profile.nameNode? records = some built)
    (read : Name → Option ByteArray) :
    (∃ root staged, profile.publish layerOf records read = .ok (root, staged)) ↔
      Binding (union (graph read) (profile.byteObservations built)) :=
  Proofs.Formats.Dasl.MstPublish.publish_accepts_iff hit read

theorem PublishProfile.publish_sound [DecidableEq Name] {profile : PublishProfile Name} {layerOf : Key → Nat}
    {records : List (Record Name)} {read staged : Name → Option ByteArray} {root : Name}
    (published : profile.publish layerOf records read = .ok (root, staged)) :
    ∃ built, build layerOf profile.nameNode? records = some built ∧ root = built.root ∧
      graph staged = union (graph read) (profile.byteObservations built) ∧
      Subset built.observed (profile.reference staged) ∧ Realizes layerOf (profile.reference staged) none root records :=
  Proofs.Formats.Dasl.MstPublish.publish_sound published

theorem PublishProfile.reference_binding (profile : PublishProfile Name) (read : Name → Option ByteArray) :
    Binding (profile.reference read) := (graph_binding read).push (graph_binding _)

theorem PublishProfile.reference_mono (profile : PublishProfile Name) {read extra : Name → Option ByteArray}
    (inclusion : Subset (graph read) (graph extra)) : Subset (profile.reference read) (profile.reference extra) := by
  rintro name node ⟨bytes, present, decoded⟩
  exact ⟨bytes, inclusion present, decoded⟩

theorem PublishProfile.read_sound (profile : PublishProfile Name) {read authoritative : Name → Option ByteArray}
    (included : Subset (graph read) (graph authoritative)) :
    ReadSound (profile.readShallow read) (profile.reference authoritative) :=
  Proofs.Formats.Dasl.MstPublish.read_sound profile included

/-- A partial read against any authoritative extension of the published
bytes can prove a hit or absence. A missing child is not an absence proof. -/
theorem PublishProfile.published_route_sound [DecidableEq Name] {profile : PublishProfile Name} {layerOf : Key → Nat}
    {records : List (Record Name)} {read staged partialRead extension : Name → Option ByteArray} {root : Name}
    (published : profile.publish layerOf records read = .ok (root, staged))
    (extended : Subset (graph staged) (graph extension)) (includes : Subset (graph partialRead) (graph extension))
    {key : Key} {fuel : Nat} {result : Option Name}
    (checked : route layerOf (profile.readShallow partialRead) key fuel none root = .ok result) : records.lookup key = result :=
  route_sound (profile.reference_binding extension) (profile.read_sound includes)
    ((profile.publish_sound published).choose_spec.2.2.2.2.mono (profile.reference_mono extended)) checked

end Silmaril.Formats.Dasl.Mst
