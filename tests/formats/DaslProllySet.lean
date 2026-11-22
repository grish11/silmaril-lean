module

import Silmaril.Formats.Dasl.Prolly.Set.Thms
import Silmaril.ProofFormats.DaslSyntax.HOL.Prolly.Defs
meta import Silmaril.Formats.Dasl.Prolly.Set.Defs
meta import Silmaril.ProofFormats.DaslSyntax.HOL.Prolly.Defs

open Silmaril.Formats.Dasl
open Silmaril.Formats.Dasl.Prolly
open Silmaril.Semantics.Prolly (Block)
open Silmaril.ProofFormats.DaslSyntax.HOL (hypothesisKey)
open Silmaril.Logic.HOLLight (Tm)
open scoped Silmaril.Formats.Dasl.Prolly

private def check (test : Bool) (message : String) : IO Unit :=
  unless test do throw (IO.userError message)

private def serialize {Key : Type} (codec : Encode.PartialCodec (Block Nat Key Unit) (Shallow Nat))
    (block : Block Nat Key Unit) : Wire.ReadResult (Shallow Nat) :=
  match codec.encode? block with | some value => .found value | none => .invalidWire

private def intCodec : Encode.PartialCodec (Block Nat Int64 Unit) (Shallow Nat) := setCodec intKey

private def linked : Read Nat := fun
  | 0 => serialize intCodec (.branch 1 [(1, 1), (2, 2)])
  | 1 => serialize intCodec (.leaf [(-1, ()), (1, ())])
  | 2 => serialize intCodec (.leaf [(2, ())])
  | 3 => serialize intCodec (.leaf [])
  | 4 => serialize intCodec (.leaf [(1, ()), (1, ())])
  | _ => .missing

private def proposition : Tm := .equal .bool (.fvar 0 .bool) (.fvar 0 .bool)

example : hypothesisKey.decode? (hypothesisKey.encode proposition) = some proposition := hypothesisKey.recovers _

public def main : IO Unit := do
  match closedSet intCodec linked 2 2 0 with
  | .ok view => check (view.keys == [-1, 1, 2]) "resolve the entire linked set"
  | .error _ => throw (IO.userError "expected a closed set")
  match closedSet intCodec linked 2 2 3, closedSet intCodec linked 2 2 4,
      closedSet intCodec linked 2 2 5, closedSet intCodec linked 2 1 0 with
  | .ok empty, .error (.invalidNode 4), .error (.missing 5), .error (.fuel 1) =>
    check empty.keys.isEmpty "a verified empty leaf really is empty"
  | _, _, _, _ => throw (IO.userError "duplicate, missing and fuel errors are not empty sets")
  let absentChild : Read Nat := fun name => if name = 2 then .missing else linked name
  match closedSet intCodec absentChild 2 2 0 with
  | .error (.missing 2) => pure ()
  | _ => throw (IO.userError "a missing child is not a partial set")
  let byteCodec : Encode.PartialCodec (Block Nat ByteKey Unit) (Shallow Nat) := setCodec byteKey
  let holRoot : Read Nat := fun _ => serialize byteCodec (.leaf [(hypothesisKey.encode proposition, ())])
  match closedSet byteCodec holRoot 2 1 0 with
  | .ok view => check (decide (view.keys.map hypothesisKey.decode? = [some proposition])) "HOL assumptions"
  | .error _ => throw (IO.userError "expected the HOL assumption set")

#print axioms closedMap_sound
#print axioms lookup_sound
#print axioms setNames_binding
#print axioms setNames_sound
#print axioms not_setNames_of_error
#print axioms hypothesisKey
