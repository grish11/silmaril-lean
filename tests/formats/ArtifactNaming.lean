module

import ArtifactNamingRows
import Silmaril.Formats.Dasl.Predecoded.Thms
import all Silmaril.Formats.Dasl.Wire.Defs
import Silmaril.Semantics.Naming.Table.Thms
meta import Silmaril.Formats.Dasl.Wire.Defs

open ArtifactNamingRows
open Silmaril.Formats.Dasl Silmaril.Semantics.Naming

private abbrev Name := List UInt8

private def hello : Name := name_hello
private def title : Name := name_title
private def empty : Name := name_empty

private def route (name : Name) : List Bool := Table.byteRoute name

private def rawChunk : Table ByteArray :=
  (Table.empty.set (route hello) bytes_hello.toByteArray).set (route empty) bytes_empty.toByteArray

private def objectChunk : Table ByteArray := Table.empty.set (route title) bytes_title.toByteArray

private def lookupRaw (name : Name) : Option ByteArray := rawChunk.lookup (route name)
private def lookupObject (name : Name) : Option ByteArray := objectChunk.lookup (route name)

private theorem different : route title ≠ route hello ∧ route title ≠ route empty := by decide +kernel

private theorem compatible : Table.Compatible lookupRaw lookupObject := by
  intro name first second foundRaw foundObject
  rw [lookupObject, objectChunk, Table.lookup_set] at foundObject
  by_cases same : route name = route title
  · rw [lookupRaw, rawChunk, Table.lookup_set, Table.lookup_set, same,
      ite_eq_right different.2, ite_eq_right different.1] at foundRaw
    contradiction
  · simp [same, Table.lookup] at foundObject

private def observed : Relation Name ByteArray := union (graph lookupRaw) (graph lookupObject)

example : Binding observed := Table.overlay_binding compatible

theorem namesHello : observed hello ("hello\n".toUTF8) := .inl rfl
theorem namesEmpty : observed empty ByteArray.empty := .inl rfl
theorem namesTitleBytes : observed title bytes_title.toByteArray := .inr rfl

example : title ∈ Table.namesOf (graph (Table.overlay lookupRaw lookupObject)) bytes_title.toByteArray :=
  (Table.overlay_iff compatible).mpr namesTitleBytes

private def titleValue : Shallow Wire.Cid := .string "Silmaril"

private def decodedChunk : Table (Shallow Wire.Cid) := Table.empty.set (route title) titleValue
private def lookupDecoded (name : Name) : Option (Shallow Wire.Cid) := decodedChunk.lookup (route name)

private theorem titleSerialization : Wire.Serializes titleValue bytes_title.toByteArray :=
  ⟨rfl, by with_unfolding_all rfl⟩

private theorem decoderWitness : Predecoded.Agrees lookupObject lookupDecoded := by
  intro name
  rw [lookupDecoded, decodedChunk, lookupObject, objectChunk, Table.lookup_set, Table.lookup_set]
  by_cases same : route name = route title
  · simpa only [ite_eq_left same, Option.bind_some] using titleSerialization.2.symm
  · simp [same, Table.lookup]

theorem namesTitle : graph lookupDecoded title titleValue :=
  Predecoded.lookup_of_serializes decoderWitness rfl titleSerialization

example : lookupDecoded hello = none := by rfl
example : Wire.parse? ([0xff] : List UInt8).toByteArray = none := by with_unfolding_all rfl

#print axioms Table.lookup_set
#print axioms Table.overlay_namesOf
#print axioms namesHello
#print axioms namesTitle

public def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected a path for the serialized title")
  let some bytes := Wire.render? titleValue | throw (IO.userError "title serialization failed")
  IO.FS.writeBinFile path bytes
