module

public import Silmaril.Formats.Dasl.Encode.Defs
public import Silmaril.Semantics.Naming.Thms
import Silmaril.Proofs.Formats.Dasl.Encode

public section

namespace Silmaril.Formats.Dasl.Encode

open Silmaril.Semantics.Naming

variable {Source Target Name Ref Wire : Type}

theorem TotalCodec.injective (codec : TotalCodec Source Target) : Function.Injective codec.encode := by
  intro left right same
  exact Option.some.inj ((codec.recovers left).symm.trans (same ▸ codec.recovers right))

theorem PartialCodec.functional (codec : PartialCodec Source Target) : codec.rel.Functional :=
  fun _ _ _ first second => Option.some.inj ((codec.recovers first).symm.trans (codec.recovers second))

theorem PartialCodec.deterministic (codec : PartialCodec Source Target) : codec.rel.Deterministic :=
  fun _ _ _ first second => Option.some.inj (Eq.trans (Eq.symm first) second)

theorem PartialCodec.list_roundtrip (codec : PartialCodec Source Target) {items : List Source} {encoded : List Target}
    (hit : codec.listEncode items = some encoded) : codec.listDecode encoded = some items :=
  Proofs.Formats.Dasl.Encode.partial_list_roundtrip codec hit

def PartialCodec.listCodec (codec : PartialCodec Source Target) : PartialCodec (List Source) (List Target) :=
  ⟨codec.listEncode, codec.listDecode, fun _ _ => codec.list_roundtrip⟩

def TotalCodec.listCodec (codec : TotalCodec Source Target) : TotalCodec (List Source) (List Target) :=
  ⟨codec.listEncode, codec.partial.listDecode, Proofs.Formats.Dasl.Encode.list_roundtrip codec⟩

def listOf (item : TotalCodec Source (Tree Ref Name)) : TotalCodec (List Source) (Tree Ref Name) :=
  item.listCodec.then list

def partialListOf (item : PartialCodec Source (Tree Ref Name)) : PartialCodec (List Source) (Tree Ref Name) :=
  item.listCodec.then list.partial

def TotalCodec.fieldsCodec (codec : TotalCodec Source Target) : TotalCodec (Fields Source) (Fields Target) :=
  ⟨(·.map codec.encode), (·.traverse? codec.decode?), Proofs.Formats.Dasl.Encode.fields_roundtrip codec⟩

def dictOf (item : TotalCodec Source (Tree Ref Name)) : TotalCodec (Fields Source) (Tree Ref Name) :=
  item.fieldsCodec.then dict

theorem codedNames_binding {raw : Relation Name Target} (bound : Binding raw) (codec : PartialCodec Source Target) :
    Binding (codedNames raw codec) := bound.push codec.functional

theorem codedNames_unique {raw : Relation Name Target} (unique : UniqueNames raw) (codec : PartialCodec Source Target) :
    UniqueNames (codedNames raw codec) := Proofs.Formats.Dasl.Encode.coded_unique unique

/-- Only representations produced by this encoder need a serialization witness.
For roots with child links, the selected deterministic encoder must already fix
the child names that enter the root representation. -/
theorem codedNames_unique_of_hash {raw : Relation Name Target} {codec : PartialCodec Source Target}
    (serialize : Target → Option Wire) (hash : Wire → Name)
    (checked : HashCompatible hash (push raw (graph serialize)))
    (renders : ∀ ⦃source repr⦄, codec.rel repr source → ∃ wire, serialize repr = some wire) :
    UniqueNames (codedNames raw codec) := Proofs.Formats.Dasl.Encode.coded_unique_of_hash serialize hash checked renders

end Silmaril.Formats.Dasl.Encode
