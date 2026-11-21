module

import Silmaril.Formats.Dasl.Mst.Build.Thms
meta import Silmaril.Formats.Dasl.Mst.Build.Thms

open Silmaril.Formats.Dasl

private def key (text : String) : Mst.Key := text.toUTF8.data.toList

private def input : List (Mst.Record Nat) :=
  [(key "2653ae71", 20), (key "app.bsky.feed.post/454397e440ec", 21),
   (key "app.bsky.feed.post/9adeb165882c", 22), (key "app.test/a", 23), (key "app.test/aa", 24), (key "blue", 25)]

private def fixtureName (node : Mst.Node Nat) : Option Nat :=
  match node.entries with
  | first :: _ => some first.record
  | [] => some ((node.left.map (· + 100)).getD 0)

private def read (built : Mst.Built Nat) (name : Nat) : Wire.ReadResult (Shallow Nat) :=
  match built.blocks.lookup name with
  | none => .missing
  | some node => match Mst.encodeNode? node with
    | none => .invalidWire
    | some value => .found value

public def main : IO Unit := do
  let some tree := Mst.Atproto.build fixtureName input | throw (IO.userError "expected ordered MST")
  unless tree.root == 22 && tree.blocks.length == 17 do
    throw (IO.userError "wrong maximum layer or missing intermediate layer")
  let lookup := fun text fuel => Mst.route Mst.Atproto.keyLayer (read tree) (key text) fuel none tree.root
  match lookup "app.test/aa" 9, lookup "2653ae71" 9, lookup "app.test/aaa" 9, lookup "2653ae71" 8 with
  | .ok (some 24), .ok (some 20), .ok none, .error (.fuel 20) => pure ()
  | _, _, _, _ => throw (IO.userError "routed reads must respect populated and empty gaps and fuel")
  let some empty := Mst.Atproto.build fixtureName [] | throw (IO.userError "expected empty root")
  unless empty.blocks == [(0, ⟨none, []⟩)] && (Mst.Atproto.build fixtureName (input ++ input)).isNone &&
      (Mst.Atproto.build fixtureName [([], 0)]).isNone do
    throw (IO.userError "empty root, duplicate keys, or empty key")
  unless (Mst.Atproto.build (fun node => if node.entries.isEmpty then none else fixtureName node) input).isNone do
    throw (IO.userError "failed naming of a nonempty gap must not prune it")
