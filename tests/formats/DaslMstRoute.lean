module

import Silmaril.Formats.Dasl.Mst.Route.Thms
meta import Silmaril.Formats.Dasl.Mst.Route.Thms

open Silmaril Silmaril.Formats.Dasl

private def layerOf (key : Mst.Key) : Nat := if key = [10] then 1 else 0

private def emit (node : Mst.Node Nat) : Wire.ReadResult (Shallow Nat) :=
  match Mst.encodeNode? node with | some value => .found value | none => .invalidWire

private def readRoot (childRead : Wire.ReadResult (Shallow Nat)) : Nat → Wire.ReadResult (Shallow Nat)
  | 0 => emit ⟨some 1, [⟨[10], 20, none⟩]⟩
  | 1 => childRead
  | _ => .missing

public def main : IO Unit := do
  let leaf := emit ⟨none, [⟨[6], 21, none⟩]⟩
  let lookup := fun child key fuel => Mst.route layerOf (readRoot child) key fuel none 0
  match lookup .missing [10] 1, lookup .missing [14] 1, lookup .missing [6] 2,
      lookup leaf [6] 2, lookup leaf [7] 2, lookup leaf [6] 1 with
  | .ok (some 20), .ok none, .error (.missing 1), .ok (some 21), .ok none, .error (.fuel 1) => pure ()
  | _, _, _, _, _, _ => throw (IO.userError "MST must distinguish inline hits, null gaps and unread children")
  let outside := emit ⟨none, [⟨[12], 21, none⟩]⟩
  match lookup .invalidWire [6] 2, lookup (.found .null) [6] 2, lookup outside [6] 2 with
  | .error (.invalidWire 1), .error (.invalidNode 1), .error (.invalidNode 1) => pure ()
  | _, _, _ => throw (IO.userError "MST must reject invalid encoding or a child outside its inherited gap")
