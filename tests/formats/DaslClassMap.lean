module

import Mathlib.Data.String.Basic
import Silmaril.Formats.Dasl.Encode.ClassMap.Thms
meta import Silmaril.Formats.Dasl.Encode.ClassMap.Thms

open Silmaril.Formats Silmaril.Formats.Dasl Silmaril.Semantics
open Silmaril.Formats.PER

example {Key Class : Type} (label : ClassMap Key Class) (key : Key) :
    ((ClassMap.intrinsic (fibers label) key).map fun group => (ClassMap.quotientEquiv label rfl group).val) = label key :=
  ClassMap.quotientEquiv_recovers label rfl key

private def initial : ClassMap Bool String
  | false => some "north"
  | true => none

private def relabelled : ClassMap Bool Nat
  | false => some 42
  | true => none

private theorem sameFibers : fibers initial = fibers relabelled := by
  apply PER.ext
  intro left right
  change (∃ tag, initial left = some tag ∧ initial right = some tag) ↔
    ∃ tag, relabelled left = some tag ∧ relabelled right = some tag
  cases left <;> cases right <;> simp [initial, relabelled]

example : ∃ rename : ClassMap.Used initial ≃ ClassMap.Used relabelled,
    ∀ key, (ClassMap.usedLookup initial key).map rename = ClassMap.usedLookup relabelled key :=
  (ClassMap.fibers_eq_iff_relabel initial relabelled).mp sameFibers

example : ClassMap.intrinsic (fibers initial) true = none :=
  ClassMap.intrinsic_miss _ (by simp [initial])

private def oversized : ClassMap Bool (Set Bool)
  | false => some Set.univ
  | true => some {true}

example : ¬ ClassMap.Coherent oversized := by
  intro valid
  have group := valid (key := false) (group := Set.univ) rfl
  have hit : true ∈ {other | oversized other = some Set.univ} := group ▸ Set.mem_univ true
  change oversized true = some Set.univ at hit
  have wrong : false ∈ ({true} : Set Bool) := (Option.some.inj hit).symm ▸ Set.mem_univ false
  exact (by decide : false ≠ true) wrong

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

local instance : DecidableEq (OrderedMap String Bool) := fun left right =>
  decidable_of_iff (left.entries = right.entries) ⟨OrderedMap.ext, congrArg OrderedMap.entries⟩

private def fixture {Name : Type} (profile : Wire.Profile Name) : IO Unit := do
  let source : OrderedMap String Bool := OrderedMap.ofLookupOn {"pear", "quince", "apple"} fun value =>
    some (value == "apple")
  let alternate : OrderedMap String Bool := OrderedMap.ofLookupOn source.keySet fun value =>
    (source.lookup? value).map not
  let layout : Encode.TotalCodec (OrderedMap String Bool) (Shallow Name) := Encode.classMap Encode.text Encode.boolean
  let codec := Encode.classMapWireCodec profile Encode.text Encode.boolean
  let some bytes := codec.encode? source | throw (IO.userError "heterogeneous map encoding failed")
  let some different := codec.encode? alternate | throw (IO.userError "alternate label encoding failed")
  let some decoded := codec.decode? bytes | throw (IO.userError "heterogeneous map decoding failed")
  check (decoded.entries == source.entries && (decoded.lookup? "unknown").isNone) "exact stored labels and support"
  check (bytes != different && alternate.lookup? "pear" == some true) "payload labels matter to bytes"
  let repeated := Encode.pairEntry.encode (Encode.text.encode "pear", Encode.boolean.encode true)
  check ((layout.decode? (Encode.list.encode [repeated, repeated])).isNone) "duplicate decoded keys rejected"

public def main : IO Unit := do
  fixture Wire.Profile.dasl
  fixture Wire.Profile.bdasl
