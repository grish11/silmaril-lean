module

import Silmaril.Formats.Dasl.Prolly.Route.Thms
meta import Silmaril.Formats.Dasl.Prolly.Route.Thms

open Silmaril Silmaril.Formats.Dasl
open scoped Silmaril.Formats.Dasl.Prolly

private def codec : Encode.PartialCodec (Semantics.Prolly.Block Nat Int64 String) (Shallow Nat) :=
  Prolly.blockCodec Prolly.intKey Encode.text

private def sample : Prolly.Read Nat := fun name =>
  let emit := fun block => match codec.encode? block with | some value => Wire.ReadResult.found value | none => .invalidWire
  match name with
  | 0 => emit (.branch 1 [(-1, 1), (2, 2)])
  | 1 => emit (.leaf [(-3, "left"), (-1, "middle")])
  | _ => .missing

public def main : IO Unit := do
  let lookup := Prolly.routedLookup codec sample 2
  match lookup 2 0 (-1), lookup 2 0 (-2), lookup 1 0 3, lookup 2 0 1, lookup 1 0 (-1) with
  | .ok (some "middle"), .ok none, .ok none, .error (.missing 2), .error (.fuel 1) => pure ()
  | _, _, _, _, _ => throw (IO.userError "routed lookup must distinguish partial reads from absence")
  let replaceChild := fun (result : Wire.ReadResult (Shallow Nat)) name => if name = 2 then result else sample name
  match Prolly.routedLookup codec (replaceChild .invalidWire) 2 2 0 1,
      Prolly.routedLookup codec (replaceChild (.found .null)) 2 2 0 1 with
  | .error (.invalidWire 2), .error (.invalidNode 2) => pure ()
  | _, _ => throw (IO.userError "a failed selected read must propagate its original fault")
