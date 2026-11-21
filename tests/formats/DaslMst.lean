module

import Silmaril.Formats.Dasl.Mst.Thms
import Silmaril.Formats.Dasl.Mst.Atproto.Thms
meta import Silmaril.Formats.Dasl.Mst.Atproto.Defs

open Silmaril.Formats.Dasl

private def check (condition : Bool) (label : String) : IO Unit :=
  unless condition do throw (IO.userError label)

private def keyBytes (key : String) : Mst.Key := key.toUTF8.data.toList

public def main : IO Unit := do
  let first := keyBytes "app.test/a"
  let next := keyBytes "app.test/aa"
  let deeper := keyBytes "app.test/b"
  check (Mst.Atproto.keyLayer first == 0 && Mst.Atproto.keyLayer next == 0 && Mst.Atproto.keyLayer deeper == 1) "SHA-256 group layers"
  check (((["2653ae71", "blue", "app.bsky.feed.post/454397e440ec", "app.bsky.feed.post/9adeb165882c"].map
    (Mst.Atproto.keyLayer ∘ keyBytes)) == [0, 1, 4, 8])) "published ATProto layer vectors"
  let node : Mst.Node Nat := ⟨none, [⟨first, 10, none⟩, ⟨next, 11, none⟩]⟩
  check (node.compress.entries.map Mst.WireEntry.shared == [0, 10]) "maximal prefix, including prefix keys"
  let some encoded := Mst.encodeNode? node | throw (IO.userError "MST node encoding")
  check (decide (Mst.decodeNode? encoded = some node)) "MST node roundtrip"
  match Mst.Atproto.readRoot (.found encoded), Mst.Atproto.readAt ⟨1, none, none, false⟩ (.found encoded),
      Mst.Atproto.readAt ⟨0, some first, none, false⟩ (.found encoded),
      Mst.Atproto.readRoot (Name := Nat) .missing, Mst.Atproto.readRoot (Name := Nat) .invalidWire with
  | .found _ _, .invalidNode, .invalidNode, .missing, .invalidWire => pure ()
  | _, _, _, _, _ => throw (IO.userError "MST root, layer, interval, or read distinctions")
  let some internal := Mst.encodeNode? (⟨some 7, []⟩ : Mst.Node Nat)
    | throw (IO.userError "empty intermediate node encoding")
  match Mst.Atproto.readAt ⟨1, none, none, false⟩ (.found internal), Mst.Atproto.readRoot (.found internal) with
  | .found _ _, .invalidNode => pure ()
  | _, _ => throw (IO.userError "empty intermediate nodes may not be roots")
  let noncanonical : Mst.WireNode Nat := ⟨none, [⟨0, first, 10, none⟩, ⟨0, next, 11, none⟩]⟩
  check noncanonical.expand?.isNone "reject a non-maximal shared prefix"
  let overlong : Mst.WireNode Nat := ⟨none, [⟨1, first, 10, none⟩]⟩
  check overlong.expand?.isNone "reject a prefix longer than the previous key"
  check ((Mst.decodeChild (.ref (.blob (1 : Nat)))).isNone) "reject raw child edges"
  let extra : Shallow Nat := .dict {"e", "l", "extra"} (fun _ => .null)
  check (Mst.decodeNode? extra).isNone "reject extra MST fields"
  let some emptyKey := Mst.encodeNode? (⟨none, [⟨[], 1, none⟩]⟩ : Mst.Node Nat)
    | throw (IO.userError "expected an empty-key wire shape")
  match Mst.Atproto.readRoot (.found emptyKey) with
  | .invalidNode => pure ()
  | _ => throw (IO.userError "reject an empty MST key")
