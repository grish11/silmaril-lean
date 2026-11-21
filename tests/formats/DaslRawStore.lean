module

import Silmaril.Formats.Dasl.RawStore.Thms
import Silmaril.Containers.Cas.Naming.Thms
meta import Silmaril.Formats.Dasl.RawStore.Thms
meta import Silmaril.Containers.Cas.Naming.Thms

open Silmaril.Formats.Dasl Silmaril.Formats.Dasl.RawStore Silmaril.Semantics.Naming
open Silmaril.Formats.Cbor

private def root := true
private def valid : ByteArray := ⟨#[0xF6]⟩
private def invalid := ByteArray.empty

private def decoder : Decoder Bool :=
  ⟨fun name => name = true, fun name => name = false,
    fun _ object raw => Bool.noConfusion (object.symm.trans raw),
    fun bytes => if bytes.size = 0 then none else some .null⟩

private def emptyStore : Blocks Bool := graph fun _ => none
private def single (bytes : ByteArray) : Blocks Bool := graph fun name => if name then some bytes else none
private def allowAll : Blocks Bool := fun _ _ => True

private theorem parsesValid : decoder.parse? valid = some .null := rfl
private theorem rejectsInvalid : decoder.parse? invalid = none := by decide

example (extended : Blocks Bool) : ¬ Completes decoder allowAll (single invalid) extended root :=
  no_completion_of_malformed_root (by rfl) rejectsInvalid

example (extended : Blocks Bool) :
    ¬ Completes decoder (fun name bytes => (fun _ : ByteArray => false) bytes = name) (single valid) extended root :=
  no_completion_of_rejected_present (name := root) (bytes := valid) (by rfl) (by decide)

private def cyclic : Decoder Bool := { decoder with parse? := fun _ => some (.ref (.obj root)) }

example (extended : Blocks Bool) : ¬ Completes cyclic allowAll (single valid) extended root :=
  no_completion_of_self_link (by rfl) (by rfl) (by rfl) (by rfl)

example : Completes decoder allowAll emptyStore (fill emptyStore (single valid)) root := by
  refine ⟨subset_fillMissing, fillMissing_binding (graph_binding _) (graph_binding _),
    fun _ _ _ => trivial, .null, .null, ⟨rfl, valid, .inr ⟨?_, rfl⟩, parsesValid⟩, .null⟩
  rintro ⟨_, hit⟩
  cases hit

example : (Silmaril.Containers.Cas.Store.fillMissing (fun _ : Bool => some invalid) (fun _ => some valid)) root =
    some invalid := rfl

public def main : IO Unit := do
  let objectBytes := [1, 0x71, 0x12, 32] ++ List.replicate 32 (0 : UInt8)
  let rawBytes := [1, 0x55, 0x12, 32] ++ List.replicate 32 (0 : UInt8)
  let some object := (Drisl.Cid.codec .dasl).parse? objectBytes | throw (IO.userError "object CID")
  let some raw := (Drisl.Cid.codec .dasl).parse? rawBytes | throw (IO.userError "raw CID")
  let withDefault base := Silmaril.Containers.Cas.Store.fillMissing base (fun _ => some valid)
  match Wire.readObject (withDefault (fun _ => none)) object,
      Wire.readObject (withDefault (fun _ => some invalid)) object,
      Wire.readObject (fun _ => none) object,
      Wire.readObject (fun _ => none) raw with
  | .found .null, .invalidWire, .missing, .invalidWire => pure ()
  | _, _, _, _ => throw (IO.userError "raw default must fill only an absent object block")
