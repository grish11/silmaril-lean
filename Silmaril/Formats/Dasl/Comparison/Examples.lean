module

import Silmaril.Formats.Dasl.Comparison.Thms

namespace Silmaril.Formats.Dasl

open Silmaril.Semantics.Naming

private def aliases (Name : Type) : Store Name := ⟨graph fun _ => some .null, graph fun _ => none⟩

private theorem bound (Name : Type) : (aliases Name).Binding := ⟨graph_binding _, graph_binding _⟩

private def namedNull {Name : Type} (name : Name) : Named Name := .obj name .null

private theorem expanded {Name : Type} (name : Name) :
    Expands (aliases Name) (.ref (.obj name)) (namedNull name) := .obj rfl .null

private def valid {Name : Type} (name : Name) : Named.Valid (aliases Name) :=
  ⟨namedNull name, bound Name, (expanded name).bindings_subset⟩

private def collapse : Renaming (aliases Bool) (aliases Unit) where
  names := fun _ => ()
  objects := by
    intro _ view hit
    change some (.null : Shallow Bool) = some view at hit
    cases Option.some.inj hit
    rfl
  blobs := by intro _ _ impossible; contradiction

example : (namedNull ()).Compatible (aliases Unit) :=
  (valid true).property.rename collapse (bound Unit)

example : ((valid true).rename collapse (bound Unit)).val = namedNull () := rfl

example : (PairedShallow.ofConcrete collapse.names (.ref (.obj true))).AbstractValid (aliases Unit) :=
  ⟨bound Unit, _, ((expanded true).rename_via_pair collapse).2⟩

example : Named.Relabels (fun old new => Link.map collapse.names old = new) (namedNull true) (namedNull ()) :=
  (Named.Relabels.graph_iff collapse.names).mpr rfl

private def objectOnly : Link Bool → Link Unit → Prop
  | .obj _, .obj _ => True
  | _, _ => False

example : Named.Relabels objectOnly (namedNull true) (namedNull ()) := .obj trivial .null

example : ¬ Named.Relabels objectOnly (.obj true (.blob false ByteArray.empty))
    (.obj () (.blob () ByteArray.empty)) := by
  intro step
  cases step with
  | obj _ child =>
    cases child with
    | blob missing => exact missing

private def unchecked : Named Bool := .obj true (.bool true)

example : (namedNull true).embed.shallow = unchecked.embed.shallow ∧ namedNull true ≠ unchecked :=
  ⟨rfl, by intro impossible; cases impossible⟩

example : (NamedPER.fromErasure (PER.equality Value) Bool (aliases Bool)).rel (namedNull true) (namedNull false) ∧
    ¬ (NamedPER.onStore (aliases Bool) (PER.equality (Named Bool))).rel (namedNull true) (namedNull false) := by
  refine ⟨⟨(valid true).property, (valid false).property, rfl⟩, ?_⟩
  intro related
  have impossible : namedNull true = namedNull false := related.2.2
  cases impossible

end Silmaril.Formats.Dasl
