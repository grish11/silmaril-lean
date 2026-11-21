module

import Silmaril.Formats.Dasl.Named.Thms
import Silmaril.Formats.Dasl.RawStore.Thms

namespace Silmaril.Formats.Dasl

open Silmaril.Semantics.Naming

private def raw : ByteArray := ⟨#[0x23]⟩

private def nested : Named Bool := .obj true (.list 1 fun _ => .blob true raw)

private def nestedStore : Store Bool :=
  ⟨graph fun name => if name then some (.list 1 fun _ => .ref (.blob true)) else none,
   graph fun name => if name then some raw else none⟩

example : ∃ tree : Named Bool, tree.erase = nested.erase ∧ tree.Compatible nestedStore :=
  exists_compatible_lift_iff.mpr ⟨⟨graph_binding _, graph_binding _⟩, _,
    .obj (name := true) (.list fun _ => .blob (name := true) rfl) rfl⟩

private def conflict : Named Bool := .list 2 fun index =>
  .obj true (.blob (index = 0) raw)

private theorem conflicting : conflict.Conflict :=
  .inl ⟨true, .ref (.blob true), .ref (.blob false), ⟨0, Or.inl ⟨rfl, rfl⟩⟩, ⟨1, Or.inl ⟨rfl, rfl⟩⟩,
    by intro impossible; cases impossible⟩

example : conflict.AdmittedBy conflict.observed := conflict.admitted_observed
example (store : Store Bool) : ¬conflict.Compatible store := conflicting.not_compatible

example : Named.Conflict (.list 2 fun index => Tree.blob true (if index = 0 then raw else ByteArray.empty)) :=
  .inr ⟨true, raw, ByteArray.empty, ⟨0, rfl, rfl⟩, ⟨1, rfl, rfl⟩,
    fun eq => Nat.noConfusion (congrArg ByteArray.size eq)⟩

private def freshBlobStore {Name : Type} {len : Nat}
    (pick : Fin len → Name) (payloads : Fin len → ByteArray) : Store Name :=
  ⟨fun _ _ => False, fun name bytes => ∃ index, name = pick index ∧ bytes = payloads index⟩

/-- For a flat list of blobs, an injective supply of fresh names suffices for any bytes. -/
example {Name : Type} {len : Nat} (pick : Fin len → Name) (fresh : Function.Injective pick)
    (payloads : Fin len → ByteArray) :
    ∃ tree : Named Name, tree.erase = .list len (fun index => Value.blob (payloads index)) ∧
      tree.Compatible (freshBlobStore pick payloads) := by
  apply exists_compatible_lift_iff.mpr
  refine ⟨⟨fun _ _ _ impossible _ => impossible.elim, ?_⟩, _,
    .list fun index => .blob ⟨index, rfl, rfl⟩⟩
  rintro name _ _ ⟨left, leftName, rfl⟩ ⟨right, rightName, rfl⟩
  exact congrArg payloads (fresh (leftName.symm.trans rightName))

private def decoder : RawStore.Decoder Bool :=
  ⟨fun name => name = true, fun name => name = false,
    fun _ object blob => Bool.noConfusion (object.symm.trans blob),
    fun bytes => if bytes.size = 0 then none else some .null⟩

example : ∃ tree : Named Bool, tree.erase = Value.obj .null ∧
    tree.Compatible (decoder.view (graph fun _ => some raw)) :=
  exists_compatible_lift_iff.mpr ⟨decoder.view_binding (graph_binding _), _,
    .obj .null ⟨rfl, raw, rfl, rfl⟩⟩

example : ¬ ∃ tree : Named Bool, tree.erase = Value.obj .null ∧
    tree.Compatible (decoder.view (graph fun _ => some ByteArray.empty)) := by
  intro lifted
  obtain ⟨_, _, choices⟩ := exists_compatible_lift_iff.mp lifted
  cases choices with
  | obj _ hit =>
    obtain ⟨_, bytes, stored, parses⟩ := hit
    cases stored
    contradiction

end Silmaril.Formats.Dasl
