module

import Silmaril.Formats.Dasl.NamedPER.Thms

namespace Silmaril.Formats.Dasl.NamedPER

open Silmaril.Semantics.Naming

private def aliasStore (Name : Type) : Store Name := ⟨graph fun _ => some .null, graph fun _ => none⟩

private theorem aliasBinding (Name : Type) : (aliasStore Name).Binding := ⟨graph_binding _, graph_binding _⟩

private def namedNull (name : Bool) : Named Bool := .obj name .null

private theorem aliasAdmitted (name : Bool) : (namedNull name).embed.bindings.Subset (aliasStore Bool) := by
  refine ⟨?_, fun _ _ impossible => impossible.elim⟩
  rintro _ _ (⟨_, rfl⟩ | impossible)
  · rfl
  · exact impossible.elim

private def renameAliases {Next : Type} (names : Bool → Next) : Renaming (aliasStore Bool) (aliasStore Next) where
  names := names
  objects := by
    intro name value hit
    change some (.null : Shallow Bool) = some value at hit
    cases Option.some.inj hit
    rfl
  blobs := by intro _ _ impossible; contradiction

private def collapse := renameAliases (fun _ => ())
private def swap := renameAliases Bool.not

example : (fromErasure (PER.equality Value) Bool (aliasStore Bool)).rel (namedNull true) (namedNull false) :=
  ⟨⟨aliasBinding Bool, aliasAdmitted _⟩, ⟨aliasBinding Bool, aliasAdmitted _⟩, rfl⟩

example : ¬ (fromShallow Bool (aliasStore Bool)).rel (namedNull true) (namedNull false) := by
  intro related
  have impossible : (.ref (.obj true) : Shallow Bool) = .ref (.obj false) := related.2.2
  cases impossible

example : (fromShallow Unit (aliasStore Unit)).rel (Named.rename collapse.names (namedNull true))
    (Named.rename collapse.names (namedNull false)) := by
  have related : (fromShallow Bool (aliasStore Bool)).rel (namedNull true) (namedNull true) :=
    ⟨⟨aliasBinding Bool, aliasAdmitted _⟩, ⟨aliasBinding Bool, aliasAdmitted _⟩, rfl⟩
  have mapped := fromShallow_equivariant (aliasBinding Bool) (aliasBinding Unit) collapse related
  exact mapped

private def prefersTrue : PER (Named Bool) := onStore (aliasStore Bool)
  ((PER.equality (Named Bool)).restrict fun tree => tree.embed.shallow = .ref (.obj true))

example : ¬ Respects swap prefersTrue prefersTrue := by
  intro law
  have related : prefersTrue.rel (namedNull true) (namedNull true) :=
    ⟨⟨aliasBinding Bool, aliasAdmitted _⟩, ⟨aliasBinding Bool, aliasAdmitted _⟩, rfl, rfl, rfl⟩
  have impossible : (.ref (.obj false) : Shallow Bool) = .ref (.obj true) := (law related).2.2.1
  cases impossible

example : (partialShallow (aliasStore Bool)).Dom (.ref (.blob true)) :=
  ⟨⟨aliasBinding Bool, fun _ _ impossible => impossible.elim, fun _ _ impossible => impossible.elim⟩,
   ⟨aliasBinding Bool, fun _ _ impossible => impossible.elim, fun _ _ impossible => impossible.elim⟩, rfl⟩

private def payload (name : Bool) : ByteArray := if name then ⟨#[0x23]⟩ else ByteArray.empty

private def nestedStore : Store Bool :=
  ⟨graph (fun _ => some (.ref (.blob false))), graph (fun name => some (payload name))⟩

private def toNat := Renaming.ofImage nestedStore (fun name => if name then 9 else 12)

example : Expands (nestedStore.renameImage toNat.names) (.ref (.obj 9)) (.obj 9 (.blob 12 ByteArray.empty)) :=
  Expands.rename (Expands.obj (name := true) (source := .ref (.blob false)) rfl (.blob rfl)) toNat

example (target : Store Unit) (rename : Renaming nestedStore target) : ¬ target.Binding := by
  intro bound
  have eq : payload true = payload false := rename.collapsed_blobs bound (Subsingleton.elim _ _) rfl rfl
  exact Nat.noConfusion (congrArg ByteArray.size eq)

end Silmaril.Formats.Dasl.NamedPER
